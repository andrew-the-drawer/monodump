export type ModelCapability = 'text' | 'vision' | 'code';

export type QuantLevel = 'f16' | 'q8_0' | 'q6_k' | 'q5_k_m' | 'q4_k_m' | 'q4_0';

export interface ModelFile {
  /** Absolute path once downloaded, or a huggingface repo-relative filename before download. */
  filename: string;
  sizeBytes: number;
}

export interface ModelInfo {
  id: string;
  displayName: string;
  organization: string;
  capability: ModelCapability;
  quant: QuantLevel;
  /** The main GGUF weights file. */
  file: ModelFile;
  /** Present only for vision models — the multimodal projector companion file. */
  mmproj?: ModelFile;
  /** True once the jinja chat template has been inspected and found to contain tool-call syntax. */
  supportsTools?: boolean;
  huggingFaceRepo?: string;
}

export type DownloadStatus = 'idle' | 'queued' | 'downloading' | 'completed' | 'failed';

export interface DownloadProgress {
  modelId: string;
  status: DownloadStatus;
  /** 0-1. For vision models this reflects combined GGUF + mmproj progress. */
  progress: number;
  bytesDownloaded: number;
  totalBytes: number;
  error?: string;
}

/** Curated, hand-tested models — never dump the entire HuggingFace catalog on users. */
export const RECOMMENDED_MODELS: readonly Pick<ModelInfo, 'displayName' | 'organization' | 'capability'>[] = [
  { displayName: 'Qwen 3', organization: 'Qwen', capability: 'text' },
  { displayName: 'Llama 3.2', organization: 'Meta', capability: 'text' },
  { displayName: 'Gemma 3', organization: 'Google', capability: 'text' },
  { displayName: 'SmolLM3', organization: 'HuggingFace', capability: 'text' },
  { displayName: 'Phi-4', organization: 'Microsoft', capability: 'text' },
  { displayName: 'SmolVLM 500M', organization: 'HuggingFace', capability: 'vision' },
] as const;
