import { Platform } from 'react-native';
import { NitroModules } from 'react-native-nitro-modules';
import type { ImageGen } from './ImageGen.nitro';

export type { ImageGen, ImageGenBackend, ImageGenProgress } from './ImageGen.nitro';

let cached: ImageGen | null = null;

/**
 * Lazily creates the HybridObject — never at module-import time. This
 * package registers no Android implementation at all (see nitro.json), so
 * calling `NitroModules.createHybridObject` eagerly would throw as soon as
 * any screen imports this module on Android, not just when a caller actually
 * tries to generate an image.
 */
export function getImageGen(): ImageGen {
  if (Platform.OS !== 'ios') {
    throw new Error('On-device image generation is iOS-only for now.');
  }
  if (!cached) {
    cached = NitroModules.createHybridObject<ImageGen>('ImageGen');
  }
  return cached;
}
