import type { ModelInfo, ModelCapability } from '../types/model';
import { memoryService } from './MemoryService';
import { parseModelFilename } from '../utils/modelFilename';

export interface DiscoveryFilters {
  capability?: ModelCapability;
  quant?: string;
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
  pipeline_tag?: string;
  tags?: string[];
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
    const response = await fetch(`${HF_API_BASE}/${repo.id}?blobs=true`);
    if (!response.ok) return [];
    const detail: HfModelDetail = await response.json();

    // Split weights (e.g. "-00001-of-00008.gguf") aren't a complete, loadable model on their own —
    // downloading just one part looks like a small/cheap file but fails to load.
    const isSplitPart = (name: string) => /-\d{5}-of-\d{5}\.gguf$/i.test(name);
    // Matches `token` only when it's a standalone segment of the filename — bounded by the
    // start/end or a non-alphanumeric separator. A plain `\b` isn't enough: `_` is a word
    // character in regex, so `\bimatrix\b` misses "imatrix_unsloth.gguf".
    const hasToken = (name: string, token: string) => new RegExp(`(^|[^a-z0-9])${token}([^a-z0-9]|$)`, 'i').test(name);
    // "mtp" also shows up glued onto a prefix with no separator ("FastMTP-32K.gguf"), so unlike
    // the other tokens this one can't require a boundary on both sides — a bare substring check
    // is used instead. The one legitimate exception is "noMTP" naming, meaning "the real weights,
    // built WITHOUT an embedded MTP head" — that must stay.
    const isMtpDraft = (name: string) => /mtp/i.test(name) && !/no[-_]?mtp/i.test(name);
    // Speculative-decoding draft/MTP heads are small companion models some uploaders ship
    // alongside the real weights — named "mtp" or "draft", as a prefix, folder, or suffix
    // ("mtp-foo.gguf", "MTP/foo.gguf", "foo-draft-Q4_0.gguf"). Never a full model by themselves.
    const isSpeculativeDraft = (name: string) => isMtpDraft(name) || hasToken(name, 'draft');
    // Calibration data used to produce importance-matrix quantizations — not model weights.
    const isImatrix = (name: string) => hasToken(name, 'imatrix');
    const ggufFiles = (detail.siblings ?? []).filter(
      (f) =>
        f.rfilename.toLowerCase().endsWith('.gguf') &&
        !isSplitPart(f.rfilename) &&
        !isSpeculativeDraft(f.rfilename) &&
        !isImatrix(f.rfilename)
    );
    // A repo can ship more than one mmproj variant (e.g. BF16 + F16 projector) — exclude them all
    // from weightFiles, not just whichever one `find` happens to pick.
    const mmprojFiles = ggufFiles.filter((f) => /mmproj/i.test(f.rfilename));
    const weightFiles = ggufFiles.filter((f) => !mmprojFiles.includes(f));

    // Some text-only repos host a stray mmproj file alongside their real (non-vision) quants —
    // only pair mmproj with the weights when the repo is actually published as vision-capable.
    const isVisionRepo = detail.pipeline_tag === 'image-text-to-text' || (detail.tags ?? []).some((t) => /image-text-to-text/i.test(t));
    const mmprojFile = isVisionRepo ? mmprojFiles[0] : undefined;

    const slashIndex = repo.id.indexOf('/');
    const organization = slashIndex >= 0 ? repo.id.slice(0, slashIndex) : repo.id;
    const name = slashIndex >= 0 ? repo.id.slice(slashIndex + 1) : repo.id;

    return weightFiles.map((f) => {
      const { quant } = parseModelFilename(f.rfilename);
      return {
        id: `hf:${repo.id}:${f.rfilename}`,
        displayName: name,
        organization,
        capability: mmprojFile ? 'vision' : this.inferCapability(detail.tags ?? repo.tags),
        quant: quant ?? 'unknown',
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
