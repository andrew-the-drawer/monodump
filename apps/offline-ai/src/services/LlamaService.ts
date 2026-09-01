import { Platform } from 'react-native';
import { initLlama, LlamaContext, type RNLlamaOAICompatibleMessage } from 'llama.rn';
import type { ModelInfo } from '../types/model';
import type { GenerationSnapshot, GenerationSubscriber } from '../types/generation';
import { memoryService } from './MemoryService';
import { parseToolCalls } from '../utils/toolCallParsing';
import type { ChatMessage, ToolCall } from '../types/chat';

export interface ToolDefinitionSchema {
  type: 'function';
  function: { name: string; description: string; parameters: Record<string, unknown> };
}

export interface GenerateOptions {
  /** Full conversation so far, ending with the newest user or tool-result turn to respond to. */
  messages: ChatMessage[];
  /** Attaches to the last message in `messages` (must be a user turn), for vision turns. */
  imageUri?: string;
  systemPrompt?: string;
  /** Only sent when the loaded model's chat template actually supports tool calls — see detectToolSupport. */
  tools?: ToolDefinitionSchema[];
  onToken?: (piece: string) => void;
}

/**
 * Flash attention on several Android GPU drivers (Adreno/Mali) produces garbage
 * output or crashes when GPU offload is also enabled — Android stays CPU-only
 * until that's sorted per-chipset. iOS's Metal path doesn't have this issue.
 */
function getSafeGpuLayers(): number {
  return Platform.OS === 'ios' ? 99 : 0;
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
  private context: LlamaContext | null = null;

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

    if (this.context) {
      await this.context.release();
      this.context = null;
      this.loadedModel = null;
    }

    this.context = await initLlama({
      model: model.file.filename,
      n_ctx: 4096,
      n_gpu_layers: getSafeGpuLayers(),
      use_mlock: true,
    });

    if (model.mmproj) {
      await this.context.initMultimodal({ path: model.mmproj.filename, use_gpu: true });
    }

    model.supportsTools = this.detectToolSupport(this.context);
    this.loadedModel = model;
  }

  /**
   * Uses the structured capability flags llama.rn derives from the model's jinja
   * chat template — never inject tool defs a model can't use, it'll hallucinate calls.
   */
  private detectToolSupport(context: LlamaContext): boolean {
    const jinja = context.model.chatTemplates?.jinja;
    if (!jinja) return false;
    return !!(jinja.toolUse || jinja.defaultCaps?.toolCalls || jinja.toolUseCaps?.toolCalls);
  }

  async generate(options: GenerateOptions): Promise<{ text: string; toolCalls: ToolCall[] }> {
    if (!this.context) throw new Error('No model loaded');
    if (options.messages.length === 0) throw new Error('generate() requires at least one message');

    this.setSnapshot({ isGenerating: true, streamingText: '' });
    try {
      const messages: RNLlamaOAICompatibleMessage[] = [];
      if (options.systemPrompt) messages.push({ role: 'system', content: options.systemPrompt });

      const lastIndex = options.messages.length - 1;
      options.messages.forEach((turn, index) => {
        if (turn.role !== 'user' && turn.role !== 'assistant' && turn.role !== 'tool') return;

        if (index === lastIndex && turn.role === 'user' && options.imageUri) {
          messages.push({
            role: 'user',
            content: [
              { type: 'text', text: turn.content },
              { type: 'image_url', image_url: { url: options.imageUri } },
            ],
          });
          return;
        }

        messages.push({ role: turn.role, content: turn.content });
      });

      const result = await this.context.completion(
        {
          messages,
          tools: options.tools,
          jinja: !!options.tools?.length,
          n_predict: 1024,
        },
        (data) => {
          this.setSnapshot({ streamingText: this.snapshot.streamingText + data.token });
          options.onToken?.(data.token);
        }
      );

      const text = result.content || result.text || '';
      const toolCalls = parseToolCalls(text, result.tool_calls);
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
    await this.context?.stopCompletion();
    this.setSnapshot({ isGenerating: false });
  }

  /** Explicit, separate from stopGeneration — only call this when truly starting a fresh context. */
  async clearContext(): Promise<void> {
    await this.context?.clearCache(true);
  }

  async release(): Promise<void> {
    await this.context?.release();
    this.context = null;
    this.loadedModel = null;
  }
}

export const llamaService = new LlamaService();
