import type { ModelInfo, ModelCapability, QuantLevel } from '../types/model';
import { memoryService } from './MemoryService';

export interface DiscoveryFilters {
  capability?: ModelCapability;
  quant?: QuantLevel;
  organization?: string;
  /** Only return models that will fit on this device, per the same 60% budget used at load time. */
  requireFitsDevice?: boolean;
}

const HF_API_BASE = 'https://huggingface.co/api/models';

/**
 * Wraps the HuggingFace models API. The important part is filtering BEFORE
 * the user downloads 4GB over cellular for a model that won't even load.
 */
class ModelDiscoveryService {
  async search(query: string, filters: DiscoveryFilters = {}): Promise<ModelInfo[]> {
    // TODO: const response = await fetch(`${HF_API_BASE}?search=${encodeURIComponent(query)}&filter=gguf`);
    // Map the HF response into ModelInfo, then apply the same filters below.
    const results: ModelInfo[] = [];
    return this.applyFilters(results, filters);
  }

  private async applyFilters(models: ModelInfo[], filters: DiscoveryFilters): Promise<ModelInfo[]> {
    let filtered = models;

    if (filters.capability) filtered = filtered.filter((m) => m.capability === filters.capability);
    if (filters.quant) filtered = filtered.filter((m) => m.quant === filters.quant);
    if (filters.organization) filtered = filtered.filter((m) => m.organization === filters.organization);

    if (filters.requireFitsDevice) {
      const checks = await Promise.all(
        filtered.map(async (m) => {
          const combinedSize = m.file.sizeBytes + (m.mmproj?.sizeBytes ?? 0);
          const budget = await memoryService.checkModelLoad(combinedSize, m.capability);
          return budget.status !== 'block';
        })
      );
      filtered = filtered.filter((_, i) => checks[i]);
    }

    return filtered;
  }
}

export const modelDiscoveryService = new ModelDiscoveryService();
