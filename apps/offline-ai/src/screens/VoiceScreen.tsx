import { useCallback } from 'react';
import { StyleSheet, Text, TouchableOpacity, View } from 'react-native';
import { whisperService } from '../services/WhisperService';
import { useWhisperStore } from '../stores/useWhisperStore';
import { useServiceSnapshot } from '../hooks/useServiceSnapshot';
import type { WhisperModelSize, WhisperSnapshot } from '../services/WhisperService';

const SIZES: WhisperModelSize[] = ['tiny', 'base', 'small'];

export default function VoiceScreen() {
  const snapshot = useServiceSnapshot<WhisperSnapshot>(
    useCallback((listener) => whisperService.subscribe(listener), []),
    useCallback(() => whisperService.getSnapshot(), [])
  );
  const { selectedSize, setSelectedSize } = useWhisperStore();

  const handleToggleRecording = async () => {
    if (snapshot.isRecording) {
      await whisperService.stopRecording();
    } else {
      await whisperService.loadModel(selectedSize);
      await whisperService.startRecording();
    }
  };

  return (
    <View style={styles.container}>
      <View style={styles.sizeRow}>
        {SIZES.map((size) => (
          <TouchableOpacity
            key={size}
            style={[styles.sizeChip, selectedSize === size && styles.sizeChipActive]}
            onPress={() => setSelectedSize(size)}
            disabled={snapshot.isRecording}
          >
            <Text style={selectedSize === size ? styles.sizeChipTextActive : styles.sizeChipText}>{size}</Text>
          </TouchableOpacity>
        ))}
      </View>

      <View style={styles.transcriptBox}>
        <Text style={styles.transcript}>{snapshot.partialText || snapshot.finalText || 'Transcript will appear here as you speak'}</Text>
      </View>

      <TouchableOpacity
        style={[styles.recordButton, snapshot.isRecording && styles.recordButtonActive]}
        onPress={handleToggleRecording}
      >
        <Text style={styles.recordButtonText}>{snapshot.isRecording ? 'Stop' : 'Record'}</Text>
      </TouchableOpacity>
    </View>
  );
}

const styles = StyleSheet.create({
  container: { flex: 1, padding: 16, gap: 16 },
  sizeRow: { flexDirection: 'row', gap: 8 },
  sizeChip: { paddingHorizontal: 12, paddingVertical: 6, borderRadius: 16, backgroundColor: '#F3F4F6' },
  sizeChipActive: { backgroundColor: '#2563EB' },
  sizeChipText: { color: '#374151' },
  sizeChipTextActive: { color: 'white' },
  transcriptBox: { flex: 1, backgroundColor: '#F3F4F6', borderRadius: 8, padding: 16 },
  transcript: { fontSize: 16, color: '#111827' },
  recordButton: { backgroundColor: '#2563EB', borderRadius: 32, paddingVertical: 16, alignItems: 'center' },
  recordButtonActive: { backgroundColor: '#DC2626' },
  recordButtonText: { color: 'white', fontWeight: '700', fontSize: 16 },
});
