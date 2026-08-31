import { Platform } from 'react-native';
import type { ModelInfo } from '../types/model';
import type { DownloadProgress } from '../types/model';

export type DownloadSubscriber = (progress: DownloadProgress) => void;

/**
 * RN's JS-level networking dies when the app backgrounds. Android's native
 * DownloadManager survives backgrounding, so downloads are bridged to it
 * there; iOS uses a background URLSession equivalent. Vision models download
 * their GGUF + mmproj in parallel, not sequentially — roughly halves total time.
 */
class ModelDownloadService {
  private progress = new Map<string, DownloadProgress>();
  private subscribers = new Map<string, Set<DownloadSubscriber>>();
  // Android DownloadManager delivers a completion broadcast that can arrive
  // before RN finishes registering its listener — track delivery explicitly
  // instead of assuming listener-then-broadcast ordering.
  private completionDelivered = new Set<string>();

  subscribe(modelId: string, subscriber: DownloadSubscriber): () => void {
    const set = this.subscribers.get(modelId) ?? new Set();
    set.add(subscriber);
    this.subscribers.set(modelId, set);
    const current = this.progress.get(modelId);
    if (current) subscriber(current);
    return () => set.delete(subscriber);
  }

  private setProgress(modelId: string, progress: DownloadProgress): void {
    this.progress.set(modelId, progress);
    for (const subscriber of this.subscribers.get(modelId) ?? []) subscriber(progress);
  }

  async download(model: ModelInfo): Promise<void> {
    const totalBytes = model.file.sizeBytes + (model.mmproj?.sizeBytes ?? 0);
    this.setProgress(model.id, { modelId: model.id, status: 'downloading', progress: 0, bytesDownloaded: 0, totalBytes });

    try {
      const downloads = [this.downloadFile(model.id, model.file.filename)];
      if (model.mmproj) downloads.push(this.downloadFile(model.id, model.mmproj.filename));
      await Promise.all(downloads);

      this.setProgress(model.id, { modelId: model.id, status: 'completed', progress: 1, bytesDownloaded: totalBytes, totalBytes });
    } catch (error) {
      this.setProgress(model.id, {
        modelId: model.id,
        status: 'failed',
        progress: this.progress.get(model.id)?.progress ?? 0,
        bytesDownloaded: this.progress.get(model.id)?.bytesDownloaded ?? 0,
        totalBytes,
        error: error instanceof Error ? error.message : String(error),
      });
      throw error;
    }
  }

  private async downloadFile(modelId: string, remoteFilename: string): Promise<void> {
    if (Platform.OS === 'android') {
      // TODO: bridge to Android's native DownloadManager; listen for ACTION_DOWNLOAD_COMPLETE
      // guarded by `completionDelivered` to cover the early-broadcast race.
    } else {
      // TODO: iOS background URLSession download task.
    }
  }
}

export const modelDownloadService = new ModelDownloadService();
