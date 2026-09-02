// Quant tokens look like Q4_K_M, IQ2_XS, Q4_0, BF16, F16 — a Q/IQ prefix plus a digit, or a
// bare F16/BF16/F32, optionally followed by underscore-joined suffix letters (K, M, S, L, XS,
// XXS, XL, P, NL, ...). Uploaders keep inventing new suffix letters (Q4_K_P, UD-Q4_K_XL), so
// this matches the general shape rather than an enumerated list.
const QUANT_TOKEN = /(^|[^a-z0-9])((?:iq[1-4]|q[0-9]|bf16|f16|f32)(?:_[a-z0-9]+)*)([^a-z0-9]|$)/i;

/**
 * Best-effort parse of a .gguf filename into a display name and quant label, for local imports
 * and HuggingFace search results alike. Returns the raw quant substring as found in the
 * filename — not normalized against a fixed list, since real-world quant naming is a moving
 * target (new IQ variants and uploader-specific suffixes show up constantly).
 */
export function parseModelFilename(filename: string): { name: string; quant: string | null } {
  const base = filename.replace(/\.gguf$/i, '');

  const match = base.match(QUANT_TOKEN);
  const quant = match ? match[2] : null;

  let name = base;
  if (quant && match) {
    const quantStart = match.index! + match[1].length;
    name = base.slice(0, quantStart).replace(/[-_.]+$/, '');
  }

  return { name: name || base, quant };
}

/** A vision model's mmproj companion is named consistently enough to guess when a link breaks. */
export function guessMmprojFilename(mainFilename: string): string {
  const base = mainFilename.replace(/\.gguf$/i, '');
  return `mmproj-${base}.gguf`;
}
