import { create } from 'zustand';
import { Directory, File, Paths } from 'expo-file-system';
import type { DownloadProgress, ModelInfo } from '../types/model';

const modelsDirectory = new Directory(Paths.document, 'models');
const catalogFile = new File(modelsDirectory, 'catalog.json');

/**
 * Downloaded/imported model weights already live on disk under `models/` — this is just the
 * metadata (display name, quant, capability, ...) needed to list them again without re-hitting
 * HuggingFace. Kept as a flat JSON file next to the weights rather than AsyncStorage, since the
 * app already manages that directory directly via expo-file-system.
 */
function loadCatalog(): ModelInfo[] {
  if (!catalogFile.exists) return [];
  try {
    const models: ModelInfo[] = JSON.parse(catalogFile.textSync());
    // Drop entries whose backing file(s) are gone (deleted outside the app, interrupted write, etc.)
    // — an entry the app can't actually load is worse than no entry.
    return models.filter((m) => new File(m.file.filename).exists && (!m.mmproj || new File(m.mmproj.filename).exists));
  } catch {
    return [];
  }
}

function saveCatalog(models: ModelInfo[]): void {
  if (!modelsDirectory.exists) modelsDirectory.create({ idempotent: true });
  catalogFile.write(JSON.stringify(models));
}

interface ModelStore {
  downloadedModels: ModelInfo[];
  discoveryResults: ModelInfo[];
  downloads: Record<string, DownloadProgress>;
  addDownloadedModel: (model: ModelInfo) => void;
  removeDownloadedModel: (modelId: string) => void;
  setDiscoveryResults: (models: ModelInfo[]) => void;
  setDownloadProgress: (progress: DownloadProgress) => void;
}

export const useModelStore = create<ModelStore>((set) => ({
  downloadedModels: loadCatalog(),
  discoveryResults: [],
  downloads: {},
  addDownloadedModel: (model) =>
    set((state) => {
      const downloadedModels = [...state.downloadedModels.filter((m) => m.id !== model.id), model];
      saveCatalog(downloadedModels);
      return { downloadedModels };
    }),
  removeDownloadedModel: (modelId) =>
    set((state) => {
      const downloadedModels = state.downloadedModels.filter((m) => m.id !== modelId);
      saveCatalog(downloadedModels);
      return { downloadedModels };
    }),
  setDiscoveryResults: (models) => set({ discoveryResults: models }),
  setDownloadProgress: (progress) => set((state) => ({ downloads: { ...state.downloads, [progress.modelId]: progress } })),
}));
