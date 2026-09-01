import { Directory, DownloadTask, File, Paths } from 'expo-file-system';
import type { DownloadProgress, ModelInfo } from '../types/model';

export type DownloadSubscriber = (progress: DownloadProgress) => void;

const modelsDirectory = new Directory(Paths.document, 'models');

/**
 * Backed by expo-file-system's DownloadTask, which is the cross-platform
 * equivalent of what used to require hand-written native bridges here:
 * `sessionType: 'background'` maps to a real background NSURLSession on iOS,
 * and progress/cancellation are handled uniformly on both platforms. Vision
 * models download their GGUF + mmproj in parallel, not sequentially —
 * roughly halves total time.
 */
class ModelDownloadService {
  private progress = new Map<string, DownloadProgress>();
  private subscribers = new Map<string, Set<DownloadSubscriber>>();
  private activeTasks = new Map<string, DownloadTask[]>();

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

  /** Resolves to a copy of `model` whose file/mmproj filenames point at the downloaded local files. */
  async download(model: ModelInfo): Promise<ModelInfo> {
    if (!model.huggingFaceRepo) {
      throw new Error(`"${model.displayName}" has no download source — was it already imported locally?`);
    }

    if (!modelsDirectory.exists) modelsDirectory.create({ idempotent: true });

    const totalBytes = model.file.sizeBytes + (model.mmproj?.sizeBytes ?? 0);
    const bytesByFile = new Map<string, number>();
    this.setProgress(model.id, { modelId: model.id, status: 'downloading', progress: 0, bytesDownloaded: 0, totalBytes });

    const reportProgress = (remoteFilename: string, bytesWritten: number) => {
      bytesByFile.set(remoteFilename, bytesWritten);
      const bytesDownloaded = [...bytesByFile.values()].reduce((sum, b) => sum + b, 0);
      this.setProgress(model.id, {
        modelId: model.id,
        status: 'downloading',
        progress: totalBytes > 0 ? bytesDownloaded / totalBytes : 0,
        bytesDownloaded,
        totalBytes,
      });
    };

    try {
      const [file, mmprojFile] = await Promise.all([
        this.downloadFile(model.id, model.huggingFaceRepo, model.file.filename, reportProgress),
        model.mmproj ? this.downloadFile(model.id, model.huggingFaceRepo, model.mmproj.filename, reportProgress) : Promise.resolve(undefined),
      ]);

      this.setProgress(model.id, { modelId: model.id, status: 'completed', progress: 1, bytesDownloaded: totalBytes, totalBytes });

      return {
        ...model,
        file: { filename: file.uri, sizeBytes: file.size ?? model.file.sizeBytes },
        mmproj: mmprojFile && model.mmproj ? { filename: mmprojFile.uri, sizeBytes: mmprojFile.size ?? model.mmproj.sizeBytes } : undefined,
      };
    } catch (error) {
      const current = this.progress.get(model.id);
      this.setProgress(model.id, {
        modelId: model.id,
        status: 'failed',
        progress: current?.progress ?? 0,
        bytesDownloaded: current?.bytesDownloaded ?? 0,
        totalBytes,
        error: error instanceof Error ? error.message : String(error),
      });
      throw error;
    } finally {
      this.activeTasks.delete(model.id);
    }
  }

  private async downloadFile(
    modelId: string,
    repo: string,
    remoteFilename: string,
    onProgress: (remoteFilename: string, bytesWritten: number) => void
  ): Promise<File> {
    // Repo-relative filenames can contain subfolders (e.g. a quant variant's own directory) — flatten for local storage.
    const localFilename = remoteFilename.replace(/[\\/]/g, '_');
    const destination = new File(modelsDirectory, localFilename);
    if (destination.exists) destination.delete();

    const task = new DownloadTask(`https://huggingface.co/${repo}/resolve/main/${remoteFilename}`, destination, {
      sessionType: 'background',
      onProgress: ({ bytesWritten }) => onProgress(remoteFilename, bytesWritten),
    });

    const tasks = this.activeTasks.get(modelId) ?? [];
    tasks.push(task);
    this.activeTasks.set(modelId, tasks);

    const file = await task.downloadAsync();
    if (!file) throw new Error(`Download of ${remoteFilename} was interrupted.`);
    return file;
  }

  cancel(modelId: string): void {
    for (const task of this.activeTasks.get(modelId) ?? []) task.cancel();
  }
}

export const modelDownloadService = new ModelDownloadService();
