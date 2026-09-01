/**
 * whisper.rn 0.7.4 ships an `exports` map with no root (".") entry, even
 * though its own README documents `import ... from 'whisper.rn'` as the
 * primary API. Metro (React Native's bundler) matches the bare specifier
 * against no pattern at all, hits `PackagePathNotExportedError`, and falls
 * back to the `main`/`react-native` fields — so this resolves fine at
 * runtime. TypeScript's `moduleResolution: "bundler"` has no such fallback,
 * so the root import needs an ambient shim covering the surface
 * WhisperService.ts actually uses. Deeper subpaths (e.g.
 * `whisper.rn/realtime-transcription/RealtimeTranscriber`) resolve for real
 * under both Metro and TypeScript because they match the package's `"./*"`
 * export pattern against an actual file — import those directly instead of
 * through a directory index, which does NOT resolve under that pattern.
 */
declare module 'whisper.rn' {
  export interface WhisperContext {
    transcribeData(
      data: ArrayBuffer,
      options: Record<string, unknown>
    ): {
      stop: () => Promise<void>;
      promise: Promise<{ result: string; language: string; segments: Array<{ text: string; t0: number; t1: number }>; isAborted: boolean }>;
    };
    release(): Promise<void>;
  }

  export function initWhisper(options: { filePath: string; useGpu?: boolean }): Promise<WhisperContext>;
}

// whisper.rn's real `realtime-transcription/*` files (pulled in transitively
// once imported directly) reference the RN JSI global `global` — not
// declared anywhere else in this project.
// eslint-disable-next-line @typescript-eslint/no-explicit-any
declare const global: any;
