export const dateTimeTool = {
  name: 'date_time',
  description: "Get the current device date and time in the user's local timezone.",
  parameters: { type: 'object', properties: {}, required: [] },
  execute: async (): Promise<string> => {
    const now = new Date();
    return JSON.stringify({
      iso: now.toISOString(),
      local: now.toString(),
      timezone: Intl.DateTimeFormat().resolvedOptions().timeZone,
    });
  },
};
