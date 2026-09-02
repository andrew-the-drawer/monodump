import { Platform } from 'react-native';
import { getImageGen, type ImageGenBackend } from '@monodump/react-native-image-gen';
import { totalImageModelBytes, type ImageModelVariant } from '../types/imageModel';
import { memoryService } from './MemoryService';

export interface ImageGenSnapshot {
  isGenerating: boolean;
  /** Local URI of the latest denoising-step preview, updated every N steps so the app never looks frozen. */
  previewUri: string | null;
  step: number;
  totalSteps: number;
  resultUri: string | null;
  loadedVariantId: string | null;
}

export interface GenerateOptions {
  negativePrompt?: string;
  steps?: number;
  previewEveryNSteps?: number;
  /** Omit for a random seed. */
  seed?: number;
}

export type ImageGenSubscriber = (snapshot: ImageGenSnapshot) => void;

/**
 * Singleton wrapping the @monodump/react-native-image-gen Nitro module,
 * which itself wraps Apple's Core ML ml-stable-diffusion pipeline. iOS-only
 * for now — see that package's README for why Android (MNN/QNN) isn't
 * implemented yet. Same load-guarding / subscriber-pattern shape as
 * LlamaService, so screens never race a model load or get orphaned mid-generation
 * by navigating away.
 */
class ImageGenService {
  private loadPromise: Promise<void> | null = null;
  private loadedVariant: ImageModelVariant | null = null;

  private snapshot: ImageGenSnapshot = { isGenerating: false, previewUri: null, step: 0, totalSteps: 0, resultUri: null, loadedVariantId: null };
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

  getLoadedVariant(): ImageModelVariant | null {
    return this.loadedVariant;
  }

  /** Never throws — returns 'unsupported' on any platform without a native backend, so screens can show a message instead of crashing. */
  detectBackend(): ImageGenBackend {
    if (Platform.OS !== 'ios') return 'unsupported';
    return getImageGen().detectBackend();
  }

  /** `resourcesPath` must point at the directory produced by ImageModelDownloadService (the `.mlmodelc` bundles directly, no extra nesting). */
  async loadModel(variant: ImageModelVariant, resourcesPath: string): Promise<void> {
    if (this.loadPromise) {
      await this.loadPromise;
      if (this.loadedVariant?.id === variant.id) return;
    }

    this.loadPromise = this.doLoad(variant, resourcesPath);
    try {
      await this.loadPromise;
    } finally {
      this.loadPromise = null;
    }
  }

  private async doLoad(variant: ImageModelVariant, resourcesPath: string): Promise<void> {
    if (Platform.OS !== 'ios') {
      throw new Error('On-device image generation is iOS-only for now.');
    }

    const budget = await memoryService.checkModelLoad(totalImageModelBytes(variant), 'image');
    if (budget.status === 'block') throw new Error(budget.message);

    this.loadedVariant = null;
    this.setSnapshot({ loadedVariantId: null });
    await getImageGen().loadModel(resourcesPath);
    this.loadedVariant = variant;
    this.setSnapshot({ loadedVariantId: variant.id });
  }

  async generate(prompt: string, options: GenerateOptions = {}): Promise<string> {
    if (!this.loadedVariant) throw new Error('No image model loaded');

    const steps = options.steps ?? 20;
    const previewEveryNSteps = options.previewEveryNSteps ?? 4;
    const seed = options.seed ?? -1;

    this.setSnapshot({ isGenerating: true, step: 0, totalSteps: steps, previewUri: null, resultUri: null });
    try {
      const resultPath = await getImageGen().generate(prompt, options.negativePrompt ?? '', steps, previewEveryNSteps, seed, (progress) => {
        this.setSnapshot({ step: progress.step, totalSteps: progress.totalSteps, previewUri: `file://${progress.previewPath}` });
      });

      const resultUri = `file://${resultPath}`;
      this.setSnapshot({ resultUri });
      return resultUri;
    } finally {
      this.setSnapshot({ isGenerating: false });
    }
  }

  /** Best-effort — the native side checks this cooperatively between denoising steps, so it may take a step or two to actually stop. */
  cancelGeneration(): void {
    if (Platform.OS !== 'ios') return;
    getImageGen().cancelGeneration();
  }

  unloadModel(): void {
    if (Platform.OS === 'ios') getImageGen().unloadModel();
    this.loadedVariant = null;
    this.setSnapshot({ loadedVariantId: null });
  }
}

export const imageGenService = new ImageGenService();
