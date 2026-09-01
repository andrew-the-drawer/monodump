import { create } from 'zustand';
import type { WhisperModelSize } from '../services/WhisperService';

interface WhisperStore {
  selectedSize: WhisperModelSize;
  setSelectedSize: (size: WhisperModelSize) => void;
}

export const useWhisperStore = create<WhisperStore>((set) => ({
  selectedSize: 'base',
  setSelectedSize: (size) => set({ selectedSize: size }),
}));
