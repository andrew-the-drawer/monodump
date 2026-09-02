import DeviceInfo from 'react-native-device-info';
import { checkMemoryBudget, estimateRequiredRam, type MemoryBudgetResult } from '../utils/memoryBudget';
import type { ModelCapability } from '../types/model';

/**
 * On the iOS Simulator, `NSProcessInfo.physicalMemory` (what getTotalMemory() reads) reports the
 * host Mac's RAM, not a real iPhone's — the Simulator runs as an ordinary macOS process. Real
 * devices don't have this quirk. Without this, testing on a Simulator on a high-RAM Mac lets
 * models through that would never fit an actual iPhone. 6GB matches the base RAM tier of current
 * iPhones — conservative, not tied to any specific model.
 */
const ASSUMED_SIMULATOR_RAM_BYTES = 6 * 1024 ** 3;

/**
 * Single source of truth for "will this model fit?". Every model load in
 * LlamaService/ImageGenService/WhisperService must go through here first —
 * the alternative is OOM crashes that don't reproduce on a dev flagship phone.
 */
class MemoryService {
  private cachedTotalRam: number | null = null;

  async getDeviceTotalRamBytes(): Promise<number> {
    if (this.cachedTotalRam !== null) return this.cachedTotalRam;
    const total = (await DeviceInfo.isEmulator()) ? ASSUMED_SIMULATOR_RAM_BYTES : await DeviceInfo.getTotalMemory();
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
