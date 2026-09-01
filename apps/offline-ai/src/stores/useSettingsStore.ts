import { create } from 'zustand';

export type IntentMode = 'pattern' | 'model' | 'manual-image';

interface SettingsStore {
  intentMode: IntentMode;
  toolsEnabled: boolean;
  setIntentMode: (mode: IntentMode) => void;
  setToolsEnabled: (enabled: boolean) => void;
}

/** intentMode 'manual-image' is the user override — corrects mis-detected intent without rewording. */
export const useSettingsStore = create<SettingsStore>((set) => ({
  intentMode: 'pattern',
  toolsEnabled: true,
  setIntentMode: (mode) => set({ intentMode: mode }),
  setToolsEnabled: (enabled) => set({ toolsEnabled: enabled }),
}));
