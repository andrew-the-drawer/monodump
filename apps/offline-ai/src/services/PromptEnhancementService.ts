import { llamaService } from './LlamaService';

const ENHANCEMENT_SYSTEM_PROMPT =
  'Rewrite the user prompt into a detailed ~75-word Stable Diffusion prompt. ' +
  'Include subject detail, artistic style, lighting, composition, and quality modifiers.';

/**
 * "A dog" makes a bad Stable Diffusion input; routing it through the loaded
 * text model first produces a much richer prompt. After enhancement, reset
 * the LLM via stopGeneration() — NOT clearContext()/clearing the KV cache,
 * which would make the following vision inference 30-60s slower.
 */
class PromptEnhancementService {
  async enhance(userPrompt: string): Promise<string> {
    const { text } = await llamaService.generate({
      prompt: userPrompt,
      systemPrompt: ENHANCEMENT_SYSTEM_PROMPT,
    });
    await llamaService.stopGeneration();
    return text || userPrompt;
  }
}

export const promptEnhancementService = new PromptEnhancementService();
