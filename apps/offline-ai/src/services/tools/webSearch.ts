/**
 * TODO: wire up a real search backend. On-device search has no cheap local
 * source of truth, so this is the one tool that necessarily leaves the
 * device — keep it opt-in and clearly labeled in the tools UI as needing
 * connectivity, unlike the other on-device-only tools.
 */
export const webSearchTool = {
  name: 'web_search',
  description: 'Search the web for up-to-date information. Requires network connectivity.',
  parameters: {
    type: 'object',
    properties: { query: { type: 'string' } },
    required: ['query'],
  },
  execute: async (_args: Record<string, unknown>): Promise<string> => {
    throw new Error('web_search is not implemented yet — no search backend configured.');
  },
};
