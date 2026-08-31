import type { ModelCapability } from '../types/model';

/** Warn once a load would cross 50% of device RAM, hard-block at 60%. */
export const MEMORY_WARN_RATIO = 0.5;
export const MEMORY_BLOCK_RATIO = 0.6;

/** File size x multiplier approximates runtime RAM (KV cache + activations). */
const RUNTIME_MULTIPLIER: Record<ModelCapability | 'image', number> = {
  text: 1.5,
  code: 1.5,
  vision: 1.5,
  image: 1.8,
};

export function estimateRequiredRam(fileSizeBytes: number, kind: ModelCapability | 'image'): number {
  return fileSizeBytes * RUNTIME_MULTIPLIER[kind];
}

export type MemoryBudgetStatus = 'ok' | 'warn' | 'block';

export interface MemoryBudgetResult {
  status: MemoryBudgetStatus;
  requiredBytes: number;
  deviceTotalBytes: number;
  ratio: number;
  message?: string;
}

/**
 * Must run before every model load. The alternative is the OS silently
 * killing the app under memory pressure, which reads to users as a crash.
 */
export function checkMemoryBudget(requiredBytes: number, deviceTotalBytes: number): MemoryBudgetResult {
  const ratio = deviceTotalBytes > 0 ? requiredBytes / deviceTotalBytes : 1;

  if (ratio >= MEMORY_BLOCK_RATIO) {
    return {
      status: 'block',
      requiredBytes,
      deviceTotalBytes,
      ratio,
      message: `This model needs ~${formatBytes(requiredBytes)} of RAM, more than ${Math.round(
        MEMORY_BLOCK_RATIO * 100
      )}% of your device's ${formatBytes(deviceTotalBytes)}. It won't fit — pick a smaller model or lower quantization.`,
    };
  }

  if (ratio >= MEMORY_WARN_RATIO) {
    return {
      status: 'warn',
      requiredBytes,
      deviceTotalBytes,
      ratio,
      message: `This model needs ~${formatBytes(requiredBytes)} of RAM. It should run, but other apps may get closed by the OS while it's loaded.`,
    };
  }

  return { status: 'ok', requiredBytes, deviceTotalBytes, ratio };
}

export function formatBytes(bytes: number): string {
  const gb = bytes / 1024 ** 3;
  if (gb >= 1) return `${gb.toFixed(1)}GB`;
  const mb = bytes / 1024 ** 2;
  return `${Math.round(mb)}MB`;
}
