export interface ImageModelFile {
  /** Path relative to `resourcesSubpath`, and to the HF repo root once joined with it. */
  path: string;
  sizeBytes: number;
}

export interface ImageModelVariant {
  id: string;
  displayName: string;
  subtitle: string;
  huggingFaceRepo: string;
  /** The compiled-bundles directory within the repo that `loadModel()` needs pointed at directly. */
  resourcesSubpath: string;
  files: ImageModelFile[];
}

export function totalImageModelBytes(variant: ImageModelVariant): number {
  return variant.files.reduce((sum, f) => sum + f.sizeBytes, 0);
}

interface MlmodelcSizes {
  analytics: number;
  coremldata: number;
  metadata: number;
  mil: number;
  weight: number;
}

/** Every Core ML `.mlmodelc` bundle HF-side has this same five-file shape — only the sizes differ per component/variant. */
function mlmodelcFiles(component: string, sizes: MlmodelcSizes): ImageModelFile[] {
  return [
    { path: `${component}.mlmodelc/analytics/coremldata.bin`, sizeBytes: sizes.analytics },
    { path: `${component}.mlmodelc/coremldata.bin`, sizeBytes: sizes.coremldata },
    { path: `${component}.mlmodelc/metadata.json`, sizeBytes: sizes.metadata },
    { path: `${component}.mlmodelc/model.mil`, sizeBytes: sizes.mil },
    { path: `${component}.mlmodelc/weights/weight.bin`, sizeBytes: sizes.weight },
  ];
}

const TOKENIZER_FILES: ImageModelFile[] = [
  { path: 'merges.txt', sizeBytes: 524657 },
  { path: 'vocab.json', sizeBytes: 862328 },
];

/**
 * Curated, hand-verified against HuggingFace's API (siblings + blob sizes) —
 * never point users at an unverified repo path for a multi-GB download. Only
 * two variants, matching the ref writeup's guidance: a small palettized
 * (6-bit) one that's the sane default on any 6-8GB phone, and the full fp16
 * one for devices with headroom. Both use split-einsum attention (tuned for
 * the Neural Engine) and pre-compiled `.mlmodelc` bundles, never the
 * `.mlpackage` originals — compiling those on-device adds tens of seconds to
 * every first load.
 */
export const RECOMMENDED_IMAGE_MODELS: ImageModelVariant[] = [
  {
    id: 'sd15-palettized-split-einsum-v2',
    displayName: 'Stable Diffusion 1.5 (palettized)',
    subtitle: '6-bit, ~1.5GB — fits comfortably on 6-8GB phones',
    huggingFaceRepo: 'apple/coreml-stable-diffusion-v1-5-palettized',
    resourcesSubpath: 'split_einsum_v2/compiled',
    files: [
      ...mlmodelcFiles('SafetyChecker', { analytics: 207, coremldata: 1415, metadata: 4339, mil: 374111, weight: 607990114 }),
      ...mlmodelcFiles('TextEncoder', { analytics: 207, coremldata: 825, metadata: 2771, mil: 208229, weight: 139866304 }),
      ...mlmodelcFiles('Unet', { analytics: 207, coremldata: 1207, metadata: 3705, mil: 3040467, weight: 645167616 }),
      ...mlmodelcFiles('VAEDecoder', { analytics: 207, coremldata: 755, metadata: 2472, mil: 181386, weight: 98993280 }),
      ...mlmodelcFiles('VAEEncoder', { analytics: 207, coremldata: 761, metadata: 2460, mil: 139736, weight: 68338112 }),
      ...TOKENIZER_FILES,
    ],
  },
  {
    id: 'sd15-fp16-split-einsum-chunked',
    displayName: 'Stable Diffusion 1.5 (full precision)',
    subtitle: 'fp16, ~2.7GB — sharper output, needs more RAM headroom',
    huggingFaceRepo: 'apple/coreml-stable-diffusion-v1-5',
    resourcesSubpath: 'split_einsum/compiled',
    files: [
      ...mlmodelcFiles('SafetyChecker', { analytics: 207, coremldata: 1414, metadata: 4338, mil: 339498, weight: 607990114 }),
      ...mlmodelcFiles('TextEncoder', { analytics: 207, coremldata: 824, metadata: 2770, mil: 170475, weight: 246145536 }),
      // Chunked Unet (not the monolithic Unet.mlmodelc) — StableDiffusionPipeline
      // auto-detects this layout, and it roughly halves peak memory during load
      // versus the single 1.7GB Unet.mlmodelc, which matters more on a phone
      // than the doubled file count does.
      ...mlmodelcFiles('UnetChunk1', { analytics: 207, coremldata: 528, metadata: 5946, mil: 687756, weight: 887680576 }),
      ...mlmodelcFiles('UnetChunk2', { analytics: 207, coremldata: 594, metadata: 6054, mil: 829605, weight: 831664384 }),
      ...mlmodelcFiles('VAEDecoder', { analytics: 207, coremldata: 754, metadata: 2471, mil: 174067, weight: 99039232 }),
      ...mlmodelcFiles('VAEEncoder', { analytics: 207, coremldata: 761, metadata: 2460, mil: 135576, weight: 68370240 }),
      ...TOKENIZER_FILES,
    ],
  },
];
