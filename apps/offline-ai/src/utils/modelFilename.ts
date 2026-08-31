import type { QuantLevel } from '../types/model';

const KNOWN_QUANTS: QuantLevel[] = ['f16', 'q8_0', 'q6_k', 'q5_k_m', 'q4_k_m', 'q4_0'];

/**
 * Best-effort parse of a local .gguf filename into a display name and quant
 * level, for users importing models they already have via the file picker.
 */
export function parseModelFilename(filename: string): { name: string; quant: QuantLevel | null } {
  const base = filename.replace(/\.gguf$/i, '');
  const lower = base.toLowerCase();

  const quant = KNOWN_QUANTS.find((q) => lower.includes(q.toLowerCase())) ?? null;

  let name = base;
  if (quant) {
    const quantIndex = lower.lastIndexOf(quant.toLowerCase());
    name = base.slice(0, quantIndex).replace(/[-_.]+$/, '');
  }

  return { name: name || base, quant };
}

/** A vision model's mmproj companion is named consistently enough to guess when a link breaks. */
export function guessMmprojFilename(mainFilename: string): string {
  const base = mainFilename.replace(/\.gguf$/i, '');
  return `mmproj-${base}.gguf`;
}
