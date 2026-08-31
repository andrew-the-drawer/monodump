// TODO: import { initWhisper, WhisperContext } from 'whisper.rn' once a dev client build exists.

export type WhisperModelSize = 'tiny' | 'base' | 'small';

export interface WhisperSnapshot {
  isRecording: boolean;
  partialText: string;
  finalText: string;
}

export type WhisperSubscriber = (snapshot: WhisperSnapshot) => void;

/**
 * Buffers audio in native memory only — never writes audio to disk, since
 * users choosing an on-device transcriber are choosing it for privacy.
 */
class WhisperService {
  private loadPromise: Promise<void> | null = null;
  private loadedSize: WhisperModelSize | null = null;
  // TODO: private context: WhisperContext | null = null;

  private snapshot: WhisperSnapshot = { isRecording: false, partialText: '', finalText: '' };
  private subscribers = new Set<WhisperSubscriber>();

  subscribe(subscriber: WhisperSubscriber): () => void {
    this.subscribers.add(subscriber);
    subscriber(this.snapshot);
    return () => this.subscribers.delete(subscriber);
  }

  getSnapshot(): WhisperSnapshot {
    return this.snapshot;
  }

  private setSnapshot(partial: Partial<WhisperSnapshot>): void {
    this.snapshot = { ...this.snapshot, ...partial };
    for (const subscriber of this.subscribers) subscriber(this.snapshot);
  }

  async loadModel(size: WhisperModelSize): Promise<void> {
    if (this.loadPromise) {
      await this.loadPromise;
      if (this.loadedSize === size) return;
    }
    this.loadPromise = this.doLoad(size);
    try {
      await this.loadPromise;
    } finally {
      this.loadPromise = null;
    }
  }

  private async doLoad(size: WhisperModelSize): Promise<void> {
    // TODO: this.context = await initWhisper({ filePath: modelPathForSize(size) });
    this.loadedSize = size;
  }

  async startRecording(): Promise<void> {
    if (!this.loadedSize) throw new Error('No whisper model loaded');
    this.setSnapshot({ isRecording: true, partialText: '', finalText: '' });
    // TODO: this.context.startRealtimeTranscribe(..., (partial) => this.setSnapshot({ partialText: partial }));
  }

  async stopRecording(): Promise<string> {
    // TODO: const final = await this.context.stopRealtimeTranscribe(); clear the native audio buffer here.
    const final = this.snapshot.partialText;
    this.setSnapshot({ isRecording: false, finalText: final, partialText: '' });
    return final;
  }
}

export const whisperService = new WhisperService();
