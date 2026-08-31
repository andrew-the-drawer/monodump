import { memoryService } from '../MemoryService';

export const deviceInfoTool = {
  name: 'device_info',
  description: 'Get basic information about the current device (RAM, platform).',
  parameters: { type: 'object', properties: {}, required: [] },
  execute: async (): Promise<string> => {
    const totalRam = await memoryService.getDeviceTotalRamBytes();
    return JSON.stringify({ totalRamBytes: totalRam });
  },
};
