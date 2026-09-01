import { requestRecordingPermissionsAsync } from 'expo-audio';
import { Directory, File, Paths, DownloadTask } from 'expo-file-system';
import { initWhisper, type WhisperContext } from 'whisper.rn';
import { RealtimeTranscriber } from 'whisper.rn/realtime-transcription/RealtimeTranscriber';
import { AudioPcmStreamAdapter } from 'whisper.rn/realtime-transcription/adapters/AudioPcmStreamAdapter';

export type WhisperModelSize = 'tiny' | 'base' | 'small';

export interface WhisperSnapshot {
  isRecording: boolean;
  partialText: string;
  finalText: string;
}

export type WhisperSubscriber = (snapshot: WhisperSnapshot) => void;

export interface WhisperModelStatus {
  size: WhisperModelSize;
  downloaded: boolean;
  bytes: number;
}

export const WHISPER_MODEL_SIZES: WhisperModelSize[] = ['tiny', 'base', 'small'];

const WHISPER_MODEL_URLS: Record<WhisperModelSize, string> = {
  tiny: 'https://huggingface.co/ggerganov/whisper.cpp/resolve/main/ggml-tiny.bin',
  base: 'https://huggingface.co/ggerganov/whisper.cpp/resolve/main/ggml-base.bin',
  small: 'https://huggingface.co/ggerganov/whisper.cpp/resolve/main/ggml-small.bin',
};

const whisperModelsDirectory = new Directory(Paths.document, 'whisper-models');

function modelFile(size: WhisperModelSize): File {
  return new File(whisperModelsDirectory, `ggml-${size}.bin`);
}

/**
 * Buffers audio in native memory only — never writes audio to disk, since
 * users choosing an on-device transcriber are choosing it for privacy.
 * Recording goes through whisper.rn's own RealtimeTranscriber, fed by
 * @fugood/react-native-audio-pcm-stream (the pairing whisper.rn ships an
 * adapter for) — there is no raw-WAV recording path on Android via Expo's
 * recorder, so this is the only cross-platform capture route.
 */
class WhisperService {
  private loadPromise: Promise<void> | null = null;
  private loadedSize: WhisperModelSize | null = null;
  private context: WhisperContext | null = null;

  private transcriber: RealtimeTranscriber | null = null;
  private sliceTexts = new Map<number, string>();

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
    if (this.context) {
      await this.context.release();
      this.context = null;
      this.loadedSize = null;
    }

    const filePath = await this.ensureModelDownloaded(size);
    this.context = await initWhisper({ filePath, useGpu: true });
    this.loadedSize = size;
  }

  private async ensureModelDownloaded(size: WhisperModelSize): Promise<string> {
    if (!whisperModelsDirectory.exists) whisperModelsDirectory.create({ idempotent: true });

    const destination = modelFile(size);
    if (destination.exists) return destination.uri;

    const task = new DownloadTask(WHISPER_MODEL_URLS[size], whisperModelsDirectory, { sessionType: 'background' });
    const file = await task.downloadAsync();
    if (!file) throw new Error(`Download of the ${size} whisper model was interrupted.`);
    return file.uri;
  }

  getModelStatus(size: WhisperModelSize): WhisperModelStatus {
    const file = modelFile(size);
    return { size, downloaded: file.exists, bytes: file.exists ? (file.size ?? 0) : 0 };
  }

  getAllModelStatuses(): WhisperModelStatus[] {
    return WHISPER_MODEL_SIZES.map((size) => this.getModelStatus(size));
  }

  /** Deletes a downloaded model's cache file, releasing it first if it's currently loaded. */
  async deleteModel(size: WhisperModelSize): Promise<void> {
    if (this.loadedSize === size && this.context) {
      await this.context.release();
      this.context = null;
      this.loadedSize = null;
    }

    const file = modelFile(size);
    if (file.exists) file.delete();
  }

  private joinSliceTexts(): string {
    return [...this.sliceTexts.entries()]
      .sort(([a], [b]) => a - b)
      .map(([, text]) => text)
      .filter(Boolean)
      .join(' ')
      .trim();
  }

  async startRecording(): Promise<void> {
    if (!this.context) throw new Error('No whisper model loaded');

    const { granted } = await requestRecordingPermissionsAsync();
    if (!granted) throw new Error('Microphone permission was denied.');

    this.sliceTexts.clear();
    this.setSnapshot({ isRecording: true, partialText: '', finalText: '' });

    this.transcriber = new RealtimeTranscriber(
      { whisperContext: this.context, audioStream: new AudioPcmStreamAdapter() },
      { audioSliceSec: 30, realtimeProcessingPauseMs: 300 },
      {
        onTranscribe: (event) => {
          if (!event.data) return;
          this.sliceTexts.set(event.sliceIndex, event.data.result);
          this.setSnapshot({ partialText: this.joinSliceTexts() });
        },
        onError: () => {
          this.setSnapshot({ isRecording: false });
        },
      }
    );

    await this.transcriber.start();
  }

  async stopRecording(): Promise<string> {
    await this.transcriber?.stop();
    this.transcriber = null;

    const final = this.joinSliceTexts();
    this.setSnapshot({ isRecording: false, finalText: final, partialText: '' });
    return final;
  }
}

export const whisperService = new WhisperService();
