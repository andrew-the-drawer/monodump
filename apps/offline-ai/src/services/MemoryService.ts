import DeviceInfo from 'react-native-device-info';
import { checkMemoryBudget, estimateRequiredRam, type MemoryBudgetResult } from '../utils/memoryBudget';
import type { ModelCapability } from '../types/model';

/**
 * Single source of truth for "will this model fit?". Every model load in
 * LlamaService/ImageGenService/WhisperService must go through here first —
 * the alternative is OOM crashes that don't reproduce on a dev flagship phone.
 */
class MemoryService {
  private cachedTotalRam: number | null = null;

  async getDeviceTotalRamBytes(): Promise<number> {
    if (this.cachedTotalRam !== null) return this.cachedTotalRam;
    const total = await DeviceInfo.getTotalMemory();
    this.cachedTotalRam = total;
    return total;
  }

  async checkModelLoad(fileSizeBytes: number, kind: ModelCapability | 'image'): Promise<MemoryBudgetResult> {
    const deviceTotal = await this.getDeviceTotalRamBytes();
    const required = estimateRequiredRam(fileSizeBytes, kind);
    return checkMemoryBudget(required, deviceTotal);
  }
}

export const memoryService = new MemoryService();
