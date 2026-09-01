import { useEffect, useState } from 'react';
import { ScrollView, StyleSheet, Switch, Text, View } from 'react-native';
import { Ionicons } from '@expo/vector-icons';
import { useSettingsStore } from '../stores/useSettingsStore';
import { useLlmStore } from '../stores/useLlmStore';
import { llamaService } from '../services/LlamaService';
import { memoryService } from '../services/MemoryService';
import { formatBytes, MEMORY_BLOCK_RATIO, MEMORY_WARN_RATIO } from '../utils/memoryBudget';
import { Button, Card, Screen, ScreenHeader, SectionLabel } from '../components/ui';
import { useTheme, spacing, typography } from '../theme/theme';

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

  useEffect(() => {
    memoryService.getDeviceTotalRamBytes().then(setTotalRam);
  }, []);

  const handleUnload = async () => {
    await llamaService.release();
    setLoadedModel(null);
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
