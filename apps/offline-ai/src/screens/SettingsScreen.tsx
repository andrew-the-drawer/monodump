import { useEffect, useState } from 'react';
import { StyleSheet, Switch, Text, View } from 'react-native';
import { useSettingsStore } from '../stores/useSettingsStore';
import { memoryService } from '../services/MemoryService';
import { formatBytes, MEMORY_BLOCK_RATIO, MEMORY_WARN_RATIO } from '../utils/memoryBudget';

export default function SettingsScreen() {
  const { toolsEnabled, setToolsEnabled } = useSettingsStore();
  const [totalRam, setTotalRam] = useState<number | null>(null);

  useEffect(() => {
    memoryService.getDeviceTotalRamBytes().then(setTotalRam);
  }, []);

  return (
    <View style={styles.container}>
      <View style={styles.row}>
        <Text style={styles.label}>Device RAM</Text>
        <Text style={styles.value}>{totalRam !== null ? formatBytes(totalRam) : '...'}</Text>
      </View>
      <View style={styles.row}>
        <Text style={styles.label}>Memory budget</Text>
        <Text style={styles.value}>
          warn {Math.round(MEMORY_WARN_RATIO * 100)}% · block {Math.round(MEMORY_BLOCK_RATIO * 100)}%
        </Text>
      </View>
      <View style={styles.row}>
        <Text style={styles.label}>Tool calling</Text>
        <Switch value={toolsEnabled} onValueChange={setToolsEnabled} />
      </View>
    </View>
  );
}

const styles = StyleSheet.create({
  container: { flex: 1, padding: 16, gap: 4 },
  row: { flexDirection: 'row', justifyContent: 'space-between', alignItems: 'center', paddingVertical: 12, borderBottomWidth: 1, borderBottomColor: '#F3F4F6' },
  label: { fontSize: 15, color: '#111827' },
  value: { fontSize: 14, color: '#6B7280' },
});
