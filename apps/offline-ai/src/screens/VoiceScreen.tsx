import { useCallback, useEffect, useRef, useState } from 'react';
import { Alert, Animated, StyleSheet, Text, TouchableOpacity, View } from 'react-native';
import { Ionicons } from '@expo/vector-icons';
import { whisperService } from '../services/WhisperService';
import { useWhisperStore } from '../stores/useWhisperStore';
import { useServiceSnapshot } from '../hooks/useServiceSnapshot';
import { Card, Screen, ScreenHeader } from '../components/ui';
import { useTheme, radius, spacing, typography } from '../theme/theme';
import type { WhisperModelSize, WhisperSnapshot } from '../services/WhisperService';

const SIZES: { value: WhisperModelSize; label: string }[] = [
  { value: 'tiny', label: 'Tiny' },
  { value: 'base', label: 'Base' },
  { value: 'small', label: 'Small' },
];

export default function VoiceScreen() {
  const { colors } = useTheme();
  const snapshot = useServiceSnapshot<WhisperSnapshot>(
    useCallback((listener) => whisperService.subscribe(listener), []),
    useCallback(() => whisperService.getSnapshot(), [])
  );
  const { selectedSize, setSelectedSize } = useWhisperStore();
  const [isPreparing, setIsPreparing] = useState(false);
  const pulse = useRef(new Animated.Value(1)).current;

  useEffect(() => {
    if (!snapshot.isRecording) {
      pulse.setValue(1);
      return;
    }
    const loop = Animated.loop(
      Animated.sequence([
        Animated.timing(pulse, { toValue: 1.15, duration: 600, useNativeDriver: true }),
        Animated.timing(pulse, { toValue: 1, duration: 600, useNativeDriver: true }),
      ])
    );
    loop.start();
    return () => loop.stop();
  }, [snapshot.isRecording, pulse]);

  const handleToggleRecording = async () => {
    if (snapshot.isRecording) {
      await whisperService.stopRecording();
      return;
    }
    setIsPreparing(true);
    try {
      await whisperService.loadModel(selectedSize);
      await whisperService.startRecording();
    } catch (error) {
      Alert.alert('Could not start recording', error instanceof Error ? error.message : String(error));
    } finally {
      setIsPreparing(false);
    }
  };

  const transcript = snapshot.partialText || snapshot.finalText;

  return (
    <Screen>
      <ScreenHeader title="Voice" subtitle="Transcription runs fully on-device" />

      <View style={styles.sizeRow}>
        {SIZES.map(({ value, label }) => {
          const active = selectedSize === value;
          return (
            <TouchableOpacity
              key={value}
              onPress={() => setSelectedSize(value)}
              disabled={snapshot.isRecording || isPreparing}
              style={[
                styles.sizeChip,
                { backgroundColor: active ? colors.primary : colors.surfaceAlt, opacity: snapshot.isRecording ? 0.5 : 1 },
              ]}
              activeOpacity={0.7}
            >
              <Text style={[typography.caption, { color: active ? colors.onPrimary : colors.textSecondary }]}>{label}</Text>
            </TouchableOpacity>
          );
        })}
      </View>

      <Card style={styles.transcriptCard}>
        <Text style={[typography.body, { color: transcript ? colors.textPrimary : colors.textMuted }]}>
          {transcript || 'Your transcript will appear here as you speak.'}
        </Text>
      </Card>

      <View style={styles.recordWrap}>
        <Animated.View style={{ transform: [{ scale: pulse }] }}>
          <TouchableOpacity
            onPress={handleToggleRecording}
            disabled={isPreparing}
            style={[
              styles.recordButton,
              { backgroundColor: snapshot.isRecording ? colors.danger : colors.primary, opacity: isPreparing ? 0.6 : 1 },
            ]}
            activeOpacity={0.85}
          >
            <Ionicons name={snapshot.isRecording ? 'stop' : 'mic'} size={30} color={colors.onPrimary} />
          </TouchableOpacity>
        </Animated.View>
        <Text style={[typography.caption, { color: colors.textMuted, marginTop: spacing.md }]}>
          {isPreparing ? 'Loading model...' : snapshot.isRecording ? 'Tap to stop' : 'Tap to record'}
        </Text>
      </View>
    </Screen>
  );
}

const styles = StyleSheet.create({
  sizeRow: { flexDirection: 'row', gap: spacing.sm, paddingHorizontal: spacing.lg, marginBottom: spacing.lg },
  sizeChip: { paddingHorizontal: spacing.lg, paddingVertical: spacing.sm, borderRadius: radius.full },
  transcriptCard: { flex: 1, marginHorizontal: spacing.lg },
  recordWrap: { alignItems: 'center', paddingVertical: spacing.xxxl },
  recordButton: { width: 76, height: 76, borderRadius: 38, alignItems: 'center', justifyContent: 'center' },
});
