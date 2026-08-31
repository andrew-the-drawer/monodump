import { Platform } from 'react-native';
import type { ModelInfo } from '../types/model';
import { memoryService } from './MemoryService';

export interface ImageGenSnapshot {
  isGenerating: boolean;
  /** Local URI of the latest denoising-step preview, updated every N steps so the app never looks frozen. */
  previewUri: string | null;
  step: number;
  totalSteps: number;
  resultUri: string | null;
}

export type ImageGenSubscriber = (snapshot: ImageGenSnapshot) => void;

type ImageBackend = 'android-qnn' | 'android-mnn' | 'ios-coreml';

/**
 * No single library covers both platforms, so backend selection is runtime,
 * not build-time: Android prefers QNN (NPU, Snapdragon 8 Gen 1+) and falls
 * back to MNN (CPU, any ARM64) when QNN is unavailable; iOS always uses
 * Core ML / Apple's ml-stable-diffusion via the Neural Engine.
 */
class ImageGenService {
  private loadPromise: Promise<void> | null = null;
  private loadedModel: ModelInfo | null = null;
  private backend: ImageBackend | null = null;

  private snapshot: ImageGenSnapshot = { isGenerating: false, previewUri: null, step: 0, totalSteps: 0, resultUri: null };
  private subscribers = new Set<ImageGenSubscriber>();

  subscribe(subscriber: ImageGenSubscriber): () => void {
    this.subscribers.add(subscriber);
    subscriber(this.snapshot);
    return () => this.subscribers.delete(subscriber);
  }

  getSnapshot(): ImageGenSnapshot {
    return this.snapshot;
  }

  private setSnapshot(partial: Partial<ImageGenSnapshot>): void {
    this.snapshot = { ...this.snapshot, ...partial };
    for (const subscriber of this.subscribers) subscriber(this.snapshot);
  }

  private async detectBackend(): Promise<ImageBackend> {
    if (Platform.OS === 'ios') return 'ios-coreml';
    // TODO: query the native side for SoC/chipset — Snapdragon 8 Gen 1+ gets QNN, everything else falls back to MNN.
    const hasQnnCapableChipset = false;
    return hasQnnCapableChipset ? 'android-qnn' : 'android-mnn';
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
    const budget = await memoryService.checkModelLoad(model.file.sizeBytes, 'image');
    if (budget.status === 'block') throw new Error(budget.message);

    this.backend = await this.detectBackend();
    // TODO: initialize the chosen native pipeline (MNN / QNN / Core ML) with model.file.filename.
    this.loadedModel = model;
  }

  async generate(prompt: string, steps = 20, previewEveryNSteps = 4): Promise<string> {
    if (!this.loadedModel || !this.backend) throw new Error('No image model loaded');

    this.setSnapshot({ isGenerating: true, step: 0, totalSteps: steps, previewUri: null, resultUri: null });
    try {
      // TODO: run the native denoising loop, calling this.setSnapshot({ step, previewUri })
      // every `previewEveryNSteps` steps via a native progress callback.
      const resultUri = '';
      this.setSnapshot({ resultUri });
      return resultUri;
    } finally {
      this.setSnapshot({ isGenerating: false });
    }
  }
}

export const imageGenService = new ImageGenService();
