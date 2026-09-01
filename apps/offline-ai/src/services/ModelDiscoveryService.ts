import type { ModelInfo, ModelCapability, QuantLevel } from '../types/model';
import { memoryService } from './MemoryService';
import { parseModelFilename } from '../utils/modelFilename';

export interface DiscoveryFilters {
  capability?: ModelCapability;
  quant?: QuantLevel;
  organization?: string;
  /** Only return models that will fit on this device, per the same 60% budget used at load time. */
  requireFitsDevice?: boolean;
}

const HF_API_BASE = 'https://huggingface.co/api/models';
/** Each match needs a follow-up request for its file listing — capped to keep search snappy on mobile data. */
const MAX_REPOS_PER_SEARCH = 10;

interface HfSearchResult {
  id: string;
  tags?: string[];
}

interface HfSibling {
  rfilename: string;
  size?: number;
}

interface HfModelDetail {
  id: string;
  siblings?: HfSibling[];
}

/**
 * Wraps the HuggingFace models API. The important part is filtering BEFORE
 * the user downloads 4GB over cellular for a model that won't even load.
 */
class ModelDiscoveryService {
  async search(query: string, filters: DiscoveryFilters = {}): Promise<ModelInfo[]> {
    const response = await fetch(`${HF_API_BASE}?search=${encodeURIComponent(query)}&filter=gguf&limit=${MAX_REPOS_PER_SEARCH}`);
    if (!response.ok) throw new Error(`HuggingFace search failed (${response.status}).`);
    const repos: HfSearchResult[] = await response.json();

    const perRepo = await Promise.all(repos.map((repo) => this.toModelInfos(repo).catch(() => [] as ModelInfo[])));
    return this.applyFilters(perRepo.flat(), filters);
  }

  /** One repo can hold several quantizations of the same weights, plus a vision model's mmproj companion. */
  private async toModelInfos(repo: HfSearchResult): Promise<ModelInfo[]> {
    const response = await fetch(`${HF_API_BASE}/${encodeURIComponent(repo.id)}?blobs=true`);
    if (!response.ok) return [];
    const detail: HfModelDetail = await response.json();

    const ggufFiles = (detail.siblings ?? []).filter((f) => f.rfilename.toLowerCase().endsWith('.gguf'));
    const mmprojFile = ggufFiles.find((f) => /mmproj/i.test(f.rfilename));
    const weightFiles = ggufFiles.filter((f) => f !== mmprojFile);

    const slashIndex = repo.id.indexOf('/');
    const organization = slashIndex >= 0 ? repo.id.slice(0, slashIndex) : repo.id;
    const name = slashIndex >= 0 ? repo.id.slice(slashIndex + 1) : repo.id;

    return weightFiles.map((f) => {
      const { quant } = parseModelFilename(f.rfilename);
      return {
        id: `hf:${repo.id}:${f.rfilename}`,
        displayName: name,
        organization,
        capability: mmprojFile ? 'vision' : this.inferCapability(repo.tags),
        quant: quant ?? 'q4_k_m',
        file: { filename: f.rfilename, sizeBytes: f.size ?? 0 },
        mmproj: mmprojFile ? { filename: mmprojFile.rfilename, sizeBytes: mmprojFile.size ?? 0 } : undefined,
        huggingFaceRepo: repo.id,
      };
    });
  }

  private inferCapability(tags?: string[]): ModelCapability {
    return tags?.some((tag) => /code/i.test(tag)) ? 'code' : 'text';
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
