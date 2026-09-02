import type { HybridObject } from 'react-native-nitro-modules';

/**
 * Only 'ios-coreml' is actually implemented right now. The 'android-mnn' /
 * 'android-qnn' members are reserved for when that backend is built — this
 * module currently has no Android implementation at all (see nitro.json and
 * README.md), so JS-side backend detection for Android is handled entirely
 * in ImageGenService without ever calling into native code.
 */
export type ImageGenBackend = 'ios-coreml' | 'android-mnn' | 'android-qnn' | 'unsupported';

export interface ImageGenProgress {
  step: number;
  totalSteps: number;
  /** Absolute filesystem path (no `file://` prefix) to a freshly written preview frame. */
  previewPath: string;
}

/**
 * Native Stable Diffusion inference. iOS-only for now — backed by Apple's
 * Core ML ml-stable-diffusion pipeline running on the Neural Engine. There is
 * no Android implementation (see nitro.json, which declares no `android`
 * platform), so this HybridObject simply isn't registered on Android; guard
 * every call site with `Platform.OS === 'ios'` rather than relying on a
 * native-side throw.
 */
export interface ImageGen extends HybridObject<{ ios: 'swift' }> {
  /** Always returns 'ios-coreml' — this HybridObject only exists on iOS. */
  detectBackend(): ImageGenBackend;

  /**
   * Compiles/warms the Core ML pipeline from a local directory of `.mlmodelc`
   * bundles (as produced by ImageModelDownloadService). Must resolve before
   * `generate()`. Safe to call again with a different path to switch models.
   */
  loadModel(resourcesPath: string): Promise<void>;

  /**
   * Runs the denoising loop. `onProgress` fires roughly every
   * `previewEveryNSteps` steps with a JPEG/PNG written to a tmp path, so the
   * UI never looks frozen during the several seconds a generation takes.
   * Resolves with the absolute path to the final PNG. Pass `seed: -1` for a
   * random seed.
   */
  generate(
    prompt: string,
    negativePrompt: string,
    steps: number,
    previewEveryNSteps: number,
    seed: number,
    onProgress: (progress: ImageGenProgress) => void
  ): Promise<string>;

  /** Best-effort cooperative cancellation, checked between denoising steps. */
  cancelGeneration(): void;

  /** Frees the loaded pipeline's memory. */
  unloadModel(): void;
}
