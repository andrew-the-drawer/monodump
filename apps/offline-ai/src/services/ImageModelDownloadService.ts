import { Directory, DownloadTask, File, Paths } from 'expo-file-system';
import { totalImageModelBytes, type ImageModelFile, type ImageModelVariant } from '../types/imageModel';

export type ImageDownloadStatus = 'idle' | 'downloading' | 'completed' | 'failed';

export interface ImageDownloadProgress {
  status: ImageDownloadStatus;
  progress: number;
  bytesDownloaded: number;
  totalBytes: number;
  error?: string;
}

export type ImageDownloadSubscriber = (progress: ImageDownloadProgress) => void;

const imageModelsDirectory = new Directory(Paths.document, 'image-models');
/** A Core ML variant is 25+ small/medium files — a handful in flight at once beats fully serial without saturating the radio. */
const DOWNLOAD_CONCURRENCY = 4;

/**
 * Unlike ModelDownloadService (one GGUF + one optional mmproj file),
 * a Core ML Stable Diffusion variant is a directory tree of 25+ files — the
 * `.mlmodelc` bundles Core ML expects are themselves directories. There's no
 * single-archive download here: HuggingFace doesn't host these variants as
 * zips (verified against the repo's file listing), so each file is fetched
 * individually into the matching local subdirectory.
 */
class ImageModelDownloadService {
  private progress = new Map<string, ImageDownloadProgress>();
  private subscribers = new Map<string, Set<ImageDownloadSubscriber>>();
  private activeTasks = new Map<string, DownloadTask[]>();
  private cancelledIds = new Set<string>();

  subscribe(variantId: string, subscriber: ImageDownloadSubscriber): () => void {
    const set = this.subscribers.get(variantId) ?? new Set();
    set.add(subscriber);
    this.subscribers.set(variantId, set);
    const current = this.progress.get(variantId);
    if (current) subscriber(current);
    return () => set.delete(subscriber);
  }

  private setProgress(variantId: string, progress: ImageDownloadProgress): void {
    this.progress.set(variantId, progress);
    for (const subscriber of this.subscribers.get(variantId) ?? []) subscriber(progress);
  }

  getProgress(variantId: string): ImageDownloadProgress | null {
    return this.progress.get(variantId) ?? null;
  }

  /** Local directory that will directly contain the `.mlmodelc` bundles once downloaded — this is what gets passed to loadModel(). */
  resourcesDirectory(variant: ImageModelVariant): Directory {
    return new Directory(imageModelsDirectory, variant.id, variant.resourcesSubpath);
  }

  /**
   * Checked against the filesystem directly, not an in-memory flag — this is
   * what makes a completed download survive an app restart, the same way
   * WhisperService.getModelStatus() checks its fixed model paths. Verifies
   * size, not just existence, so a file left behind by an interrupted
   * download (app killed mid-transfer) doesn't read as "downloaded".
   */
  isDownloaded(variant: ImageModelVariant): boolean {
    const dir = this.resourcesDirectory(variant);
    return variant.files.every((f) => {
      const file = this.localFile(dir, f);
      return file.exists && file.size === f.sizeBytes;
    });
  }

  private localFile(resourcesDir: Directory, file: ImageModelFile): File {
    const segments = file.path.split('/');
    const filename = segments.pop()!;
    let dir = resourcesDir;
    for (const segment of segments) dir = new Directory(dir, segment);
    return new File(dir, filename);
  }

  async download(variant: ImageModelVariant): Promise<string> {
    this.cancelledIds.delete(variant.id);
    const resourcesDir = this.resourcesDirectory(variant);
    const totalBytes = totalImageModelBytes(variant);
    const bytesByFile = new Map<string, number>();

    this.setProgress(variant.id, { status: 'downloading', progress: 0, bytesDownloaded: 0, totalBytes });

    const reportProgress = (path: string, bytesWritten: number) => {
      bytesByFile.set(path, bytesWritten);
      const bytesDownloaded = [...bytesByFile.values()].reduce((sum, b) => sum + b, 0);
      this.setProgress(variant.id, {
        status: 'downloading',
        progress: totalBytes > 0 ? bytesDownloaded / totalBytes : 0,
        bytesDownloaded,
        totalBytes,
      });
    };

    try {
      await this.runPool(variant.files, DOWNLOAD_CONCURRENCY, (file) => this.downloadOne(variant, resourcesDir, file, reportProgress));

      if (this.cancelledIds.has(variant.id)) {
        throw new Error('Download cancelled.');
      }

      this.setProgress(variant.id, { status: 'completed', progress: 1, bytesDownloaded: totalBytes, totalBytes });
      return resourcesDir.uri;
    } catch (error) {
      const current = this.progress.get(variant.id);
      this.setProgress(variant.id, {
        status: 'failed',
        progress: current?.progress ?? 0,
        bytesDownloaded: current?.bytesDownloaded ?? 0,
        totalBytes,
        error: error instanceof Error ? error.message : String(error),
      });
      throw error;
    } finally {
      this.activeTasks.delete(variant.id);
    }
  }

  private async downloadOne(
    variant: ImageModelVariant,
    resourcesDir: Directory,
    file: ImageModelFile,
    onProgress: (path: string, bytesWritten: number) => void
  ): Promise<void> {
    if (this.cancelledIds.has(variant.id)) return;

    const destination = this.localFile(resourcesDir, file);
    if (!destination.parentDirectory.exists) destination.parentDirectory.create({ idempotent: true, intermediates: true });

    if (destination.exists) {
      if (destination.size === file.sizeBytes) {
        onProgress(file.path, file.sizeBytes);
        return;
      }
      // Left behind by a download that was interrupted (app killed, network drop) — unlike the
      // static File.downloadFileAsync, DownloadTask has no `idempotent` option, so a stale file at
      // the destination makes downloadAsync() fail outright instead of overwriting it.
      destination.delete();
    }

    const remoteUrl = `https://huggingface.co/${variant.huggingFaceRepo}/resolve/main/${variant.resourcesSubpath}/${file.path}`;
    const task = new DownloadTask(remoteUrl, destination, {
      sessionType: 'background',
      onProgress: ({ bytesWritten }) => onProgress(file.path, bytesWritten),
    });

    const tasks = this.activeTasks.get(variant.id) ?? [];
    tasks.push(task);
    this.activeTasks.set(variant.id, tasks);

    const result = await task.downloadAsync();
    if (!result) throw new Error(`Download of ${file.path} was interrupted.`);
  }

  private async runPool<T>(items: T[], concurrency: number, worker: (item: T) => Promise<void>): Promise<void> {
    const queue = [...items];
    const lanes = Array.from({ length: Math.min(concurrency, items.length) }, async () => {
      let next: T | undefined;
      while ((next = queue.shift())) {
        await worker(next);
      }
    });
    await Promise.all(lanes);
  }

  cancel(variantId: string): void {
    this.cancelledIds.add(variantId);
    for (const task of this.activeTasks.get(variantId) ?? []) task.cancel();
  }

  async delete(variant: ImageModelVariant): Promise<void> {
    const root = new Directory(imageModelsDirectory, variant.id);
    if (root.exists) root.delete();
    this.progress.delete(variant.id);
  }
}

export const imageModelDownloadService = new ImageModelDownloadService();
