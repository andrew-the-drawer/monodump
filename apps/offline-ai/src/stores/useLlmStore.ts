import { create } from 'zustand';
import type { ChatMessage } from '../types/chat';
import type { ModelInfo } from '../types/model';

/**
 * Services write here, UI only reads. Keeping generation state in a
 * component instead of a store is tempting right up until a user switches
 * tabs mid-generation and the state disappears with the unmounted screen.
 */
interface LlmStore {
  loadedModel: ModelInfo | null;
  messages: ChatMessage[];
  setLoadedModel: (model: ModelInfo | null) => void;
  addMessage: (message: ChatMessage) => void;
  updateLastMessage: (content: string) => void;
  clearMessages: () => void;
}

export const useLlmStore = create<LlmStore>((set) => ({
  loadedModel: null,
  messages: [],
  setLoadedModel: (model) => set({ loadedModel: model }),
  addMessage: (message) => set((state) => ({ messages: [...state.messages, message] })),
  updateLastMessage: (content) =>
    set((state) => {
      if (state.messages.length === 0) return state;
      const messages = [...state.messages];
      messages[messages.length - 1] = { ...messages[messages.length - 1], content };
      return { messages };
    }),
  clearMessages: () => set({ messages: [] }),
}));
