export type Intent = 'text' | 'image';

const IMAGE_KEYWORDS = [
  'draw',
  'generate an image',
  'generate image',
  'create an image',
  'create image',
  'paint',
  'sketch',
  'picture of',
  'image of',
  'illustration of',
];

/**
 * Fast, keyword-based intent detection — the default. Misses nuance but
 * costs nothing, unlike LLM-based classification which adds latency before
 * generation even starts. See classifyIntentWithModel for the accurate path.
 */
export function classifyIntentByPattern(text: string): Intent {
  const lower = text.toLowerCase();
  return IMAGE_KEYWORDS.some((kw) => lower.includes(kw)) ? 'image' : 'text';
}

const INTENT_SYSTEM_PROMPT =
  'Classify the user message as requesting either "image" generation or "text" generation. Respond with exactly one word: image or text.';

/**
 * Slower, more accurate path: routes the prompt through the already-loaded
 * text model. `generate` is injected so this stays decoupled from LlamaService.
 */
export async function classifyIntentWithModel(
  text: string,
  generate: (prompt: string, systemPrompt: string) => Promise<string>
): Promise<Intent> {
  const response = await generate(text, INTENT_SYSTEM_PROMPT);
  return response.trim().toLowerCase().startsWith('image') ? 'image' : 'text';
}
