/**
 * Background-safe generation state, owned by a service and mirrored into a
 * Zustand store. Screens subscribe via useGenerationSubscriber instead of
 * holding generation state themselves, so navigating away never interrupts
 * an in-flight generation.
 */
export interface GenerationSnapshot {
  isGenerating: boolean;
  streamingText: string;
  tokensPerSecond?: number;
}

export type GenerationSubscriber = (snapshot: GenerationSnapshot) => void;
