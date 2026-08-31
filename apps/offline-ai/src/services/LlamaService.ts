import type { ModelInfo } from '../types/model';
import type { GenerationSnapshot, GenerationSubscriber } from '../types/generation';
import { memoryService } from './MemoryService';
import { parseToolCalls } from '../utils/toolCallParsing';
import type { ToolCall } from '../types/chat';

// TODO: import { LlamaContext, initLlama } from 'llama.rn' once a dev client build exists —
// Expo Go cannot load native modules, so this stays behind a TODO until then.

export interface GenerateOptions {
  prompt: string;
  systemPrompt?: string;
  imageUri?: string;
  onToken?: (piece: string) => void;
}

/**
 * Singleton wrapping llama.rn. Two screens racing to load different models
 * at once produces a native SIGSEGV, not a catchable JS exception — every
 * load is guarded by `loadPromise` so a second caller awaits the first
 * instead of racing it.
 */
class LlamaService {
  private loadPromise: Promise<void> | null = null;
  private loadedModel: ModelInfo | null = null;
  // TODO: private context: LlamaContext | null = null;

  private snapshot: GenerationSnapshot = { isGenerating: false, streamingText: '' };
  private subscribers = new Set<GenerationSubscriber>();

  /** Screens bind here instead of owning generation state, so navigating away never interrupts a stream. */
  subscribe(subscriber: GenerationSubscriber): () => void {
    this.subscribers.add(subscriber);
    subscriber(this.snapshot);
    return () => this.subscribers.delete(subscriber);
  }

  getSnapshot(): GenerationSnapshot {
    return this.snapshot;
  }

  private setSnapshot(partial: Partial<GenerationSnapshot>): void {
    this.snapshot = { ...this.snapshot, ...partial };
    for (const subscriber of this.subscribers) subscriber(this.snapshot);
  }

  getLoadedModel(): ModelInfo | null {
    return this.loadedModel;
  }

  async loadModel(model: ModelInfo): Promise<void> {
    if (this.loadPromise) {
      await this.loadPromise;
      if (this.loadedModel?.id === model.id) return;
    }

    this.loadPromise = this.doLoad(model);
    try {
      await this.loadPromise;
    } finally {
      this.loadPromise = null;
    }
  }

  private async doLoad(model: ModelInfo): Promise<void> {
    const budget = await memoryService.checkModelLoad(model.file.sizeBytes, model.capability);
    if (budget.status === 'block') {
      throw new Error(budget.message);
    }

    // TODO: this.context = await initLlama({
    //   model: model.file.filename,
    //   n_gpu_layers: getSafeGpuLayers(), // 0 on Android when flash attention would be enabled
    //   ...(model.mmproj ? { mmproj: model.mmproj.filename } : {}),
    // });
    // model.supportsTools = detectToolSupport(this.context.model.chatTemplate);

    this.loadedModel = model;
  }

  /** Detect tool support from the jinja chat template — never inject tool defs a model can't use, it'll hallucinate calls. */
  private detectToolSupport(chatTemplate: string): boolean {
    return /tool_call|tools\[/i.test(chatTemplate);
  }

  async generate(options: GenerateOptions): Promise<{ text: string; toolCalls: ToolCall[] }> {
    if (!this.loadedModel) throw new Error('No model loaded');

    this.setSnapshot({ isGenerating: true, streamingText: '' });
    try {
      // TODO: const result = await this.context.completion({ prompt: options.prompt, ... }, (data) => {
      //   this.setSnapshot({ streamingText: this.snapshot.streamingText + data.token });
      //   options.onToken?.(data.token);
      // });
      const text = '';
      const toolCalls = parseToolCalls(text);
      return { text, toolCalls };
    } finally {
      this.setSnapshot({ isGenerating: false });
    }
  }

  /**
   * Resets sampling state between turns WITHOUT clearing the KV cache — clearing
   * it here makes the next vision inference take 30-60s longer, because the
   * cache from the text model warms subsequent multimodal loads.
   */
  async stopGeneration(): Promise<void> {
    // TODO: await this.context?.stopCompletion();
    this.setSnapshot({ isGenerating: false });
  }

  /** Explicit, separate from stopGeneration — only call this when truly starting a fresh context. */
  async clearContext(): Promise<void> {
    // TODO: await this.context?.rewind() / release + reinit, depending on llama.rn API surface.
  }

  async release(): Promise<void> {
    // TODO: await this.context?.release();
    this.loadedModel = null;
  }
}

export const llamaService = new LlamaService();
