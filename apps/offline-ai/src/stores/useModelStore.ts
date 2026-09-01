import { create } from 'zustand';
import type { DownloadProgress, ModelInfo } from '../types/model';

interface ModelStore {
  downloadedModels: ModelInfo[];
  discoveryResults: ModelInfo[];
  downloads: Record<string, DownloadProgress>;
  addDownloadedModel: (model: ModelInfo) => void;
  setDiscoveryResults: (models: ModelInfo[]) => void;
  setDownloadProgress: (progress: DownloadProgress) => void;
}

export const useModelStore = create<ModelStore>((set) => ({
  downloadedModels: [],
  discoveryResults: [],
  downloads: {},
  addDownloadedModel: (model) => set((state) => ({ downloadedModels: [...state.downloadedModels, model] })),
  setDiscoveryResults: (models) => set({ discoveryResults: models }),
  setDownloadProgress: (progress) => set((state) => ({ downloads: { ...state.downloads, [progress.modelId]: progress } })),
}));
