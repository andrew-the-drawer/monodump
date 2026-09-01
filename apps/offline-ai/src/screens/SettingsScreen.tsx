import { useCallback, useEffect, useState } from 'react';
import { Alert, ScrollView, StyleSheet, Switch, Text, TouchableOpacity, View } from 'react-native';
import { Ionicons } from '@expo/vector-icons';
import { useFocusEffect } from '@react-navigation/native';
import { useSettingsStore } from '../stores/useSettingsStore';
import { useLlmStore } from '../stores/useLlmStore';
import { llamaService } from '../services/LlamaService';
import { memoryService } from '../services/MemoryService';
import { whisperService } from '../services/WhisperService';
import { useServiceSnapshot } from '../hooks/useServiceSnapshot';
import { formatBytes, MEMORY_BLOCK_RATIO, MEMORY_WARN_RATIO } from '../utils/memoryBudget';
import { Button, Card, Screen, ScreenHeader, SectionLabel } from '../components/ui';
import { useTheme, spacing, typography } from '../theme/theme';
import type { WhisperModelSize, WhisperModelStatus, WhisperSnapshot } from '../services/WhisperService';

const WHISPER_SIZE_LABELS: Record<WhisperModelSize, string> = { tiny: 'Tiny', base: 'Base', small: 'Small' };

function SettingsRow({ icon, label, value }: { icon: keyof typeof Ionicons.glyphMap; label: string; value: string }) {
  const { colors } = useTheme();
  return (
    <View style={styles.row}>
      <View style={styles.rowLeft}>
        <Ionicons name={icon} size={18} color={colors.textSecondary} />
        <Text style={[typography.body, { color: colors.textPrimary, marginLeft: spacing.sm }]}>{label}</Text>
      </View>
      <Text style={[typography.body, { color: colors.textSecondary }]}>{value}</Text>
    </View>
  );
}

export default function SettingsScreen() {
  const { colors } = useTheme();
  const { toolsEnabled, setToolsEnabled } = useSettingsStore();
  const { loadedModel, setLoadedModel } = useLlmStore();
  const [totalRam, setTotalRam] = useState<number | null>(null);
  const [whisperModels, setWhisperModels] = useState<WhisperModelStatus[]>(() => whisperService.getAllModelStatuses());
  const whisperSnapshot = useServiceSnapshot<WhisperSnapshot>(
    useCallback((listener) => whisperService.subscribe(listener), []),
    useCallback(() => whisperService.getSnapshot(), [])
  );

  useEffect(() => {
    memoryService.getDeviceTotalRamBytes().then(setTotalRam);
  }, []);

  // Voice models can be downloaded from the Voice tab, which stays mounted alongside this one — re-check on focus.
  useFocusEffect(
    useCallback(() => {
      setWhisperModels(whisperService.getAllModelStatuses());
    }, [])
  );

  const handleUnload = async () => {
    await llamaService.release();
    setLoadedModel(null);
  };

  const handleDeleteWhisperModel = (size: WhisperModelSize) => {
    Alert.alert('Delete model', `Remove the cached "${WHISPER_SIZE_LABELS[size]}" voice model? You can re-download it later.`, [
      { text: 'Cancel', style: 'cancel' },
      {
        text: 'Delete',
        style: 'destructive',
        onPress: async () => {
          await whisperService.deleteModel(size);
          setWhisperModels(whisperService.getAllModelStatuses());
        },
      },
    ]);
  };

  return (
    <Screen>
      <ScreenHeader title="Settings" />
      <ScrollView contentContainerStyle={{ paddingHorizontal: spacing.lg, paddingBottom: spacing.xxxl, gap: spacing.lg }}>
        <View>
          <SectionLabel>Device</SectionLabel>
          <Card style={{ gap: 0 }}>
            <SettingsRow icon="hardware-chip-outline" label="Device RAM" value={totalRam !== null ? formatBytes(totalRam) : '...'} />
            <View style={[styles.divider, { backgroundColor: colors.border }]} />
            <SettingsRow
              icon="speedometer-outline"
              label="Memory budget"
              value={`warn ${Math.round(MEMORY_WARN_RATIO * 100)}% · block ${Math.round(MEMORY_BLOCK_RATIO * 100)}%`}
            />
          </Card>
        </View>

        <View>
          <SectionLabel>Model</SectionLabel>
          <Card style={{ gap: spacing.sm }}>
            <SettingsRow icon="layers-outline" label="Loaded model" value={loadedModel?.displayName ?? 'None'} />
            {loadedModel && <Button label="Unload model" variant="outline" onPress={handleUnload} icon="log-out-outline" />}
          </Card>
        </View>

        <View>
          <SectionLabel>Voice models</SectionLabel>
          <Card style={{ gap: 0 }}>
            {whisperModels.map((model, index) => {
              return (
                <View key={model.size}>
                  {index > 0 && <View style={[styles.divider, { backgroundColor: colors.border }]} />}
                  <View style={styles.row}>
                    <View style={styles.rowLeft}>
                      <Ionicons name="mic-outline" size={18} color={colors.textSecondary} />
                      <View style={{ marginLeft: spacing.sm }}>
                        <Text style={[typography.body, { color: colors.textPrimary }]}>{WHISPER_SIZE_LABELS[model.size]}</Text>
                        <Text style={[typography.caption, { color: colors.textMuted }]}>
                          {model.downloaded ? formatBytes(model.bytes) : 'Not downloaded'}
                        </Text>
                      </View>
                    </View>
                    {model.downloaded && (
                      <TouchableOpacity
                        onPress={() => handleDeleteWhisperModel(model.size)}
                        disabled={whisperSnapshot.isRecording}
                        hitSlop={8}
                      >
                        <Ionicons
                          name="trash-outline"
                          size={18}
                          color={whisperSnapshot.isRecording ? colors.textMuted : colors.danger}
                        />
                      </TouchableOpacity>
                    )}
                  </View>
                </View>
              );
            })}
          </Card>
        </View>

        <View>
          <SectionLabel>Chat</SectionLabel>
          <Card>
            <View style={styles.row}>
              <View style={styles.rowLeft}>
                <Ionicons name="hammer-outline" size={18} color={colors.textSecondary} />
                <View style={{ marginLeft: spacing.sm }}>
                  <Text style={[typography.body, { color: colors.textPrimary }]}>Tool calling</Text>
                  <Text style={[typography.caption, { color: colors.textMuted }]}>Only used by models whose chat template supports it</Text>
                </View>
              </View>
              <Switch value={toolsEnabled} onValueChange={setToolsEnabled} trackColor={{ true: colors.primary }} />
            </View>
          </Card>
        </View>
      </ScrollView>
    </Screen>
  );
}

const styles = StyleSheet.create({
  row: { flexDirection: 'row', alignItems: 'center', justifyContent: 'space-between', paddingVertical: spacing.sm },
  rowLeft: { flexDirection: 'row', alignItems: 'center', flexShrink: 1 },
  divider: { height: StyleSheet.hairlineWidth, marginVertical: spacing.xs },
});
