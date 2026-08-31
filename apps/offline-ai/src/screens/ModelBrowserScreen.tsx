import { useState } from 'react';
import { Alert, FlatList, StyleSheet, Text, TextInput, TouchableOpacity, View } from 'react-native';
import { RECOMMENDED_MODELS } from '../types/model';
import { modelDiscoveryService } from '../services/ModelDiscoveryService';
import { modelDownloadService } from '../services/ModelDownloadService';
import { localModelImportService } from '../services/LocalModelImportService';
import { useModelStore } from '../stores/useModelStore';
import { useLlmStore } from '../stores/useLlmStore';
import { llamaService } from '../services/LlamaService';
import type { ModelInfo } from '../types/model';

export default function ModelBrowserScreen() {
  const { downloadedModels, discoveryResults, setDiscoveryResults, addDownloadedModel } = useModelStore();
  const setLoadedModel = useLlmStore((s) => s.setLoadedModel);
  const [query, setQuery] = useState('');

  const handleSearch = async () => {
    const results = await modelDiscoveryService.search(query, { requireFitsDevice: true });
    setDiscoveryResults(results);
  };

  const handleImportLocal = async () => {
    try {
      const model = await localModelImportService.pickAndImport();
      if (model) addDownloadedModel(model);
    } catch (error) {
      Alert.alert('Import failed', error instanceof Error ? error.message : String(error));
    }
  };

  const handleDownload = async (model: ModelInfo) => {
    try {
      await modelDownloadService.download(model);
      addDownloadedModel(model);
    } catch (error) {
      Alert.alert('Download failed', error instanceof Error ? error.message : String(error));
    }
  };

  const handleLoad = async (model: ModelInfo) => {
    try {
      await llamaService.loadModel(model);
      setLoadedModel(model);
    } catch (error) {
      Alert.alert("Can't load model", error instanceof Error ? error.message : String(error));
    }
  };

  return (
    <View style={styles.container}>
      <View style={styles.searchRow}>
        <TextInput style={styles.searchInput} value={query} onChangeText={setQuery} placeholder="Search HuggingFace..." onSubmitEditing={handleSearch} />
        <TouchableOpacity style={styles.searchButton} onPress={handleSearch}>
          <Text style={styles.searchButtonText}>Search</Text>
        </TouchableOpacity>
      </View>

      <TouchableOpacity style={styles.importButton} onPress={handleImportLocal}>
        <Text style={styles.importButtonText}>Import a local .gguf file</Text>
      </TouchableOpacity>

      <Text style={styles.sectionHeader}>Recommended</Text>
      <FlatList
        data={RECOMMENDED_MODELS}
        keyExtractor={(item) => item.displayName}
        horizontal
        showsHorizontalScrollIndicator={false}
        renderItem={({ item }) => (
          <View style={styles.recommendedChip}>
            <Text style={styles.recommendedName}>{item.displayName}</Text>
            <Text style={styles.recommendedMeta}>{item.organization} · {item.capability}</Text>
          </View>
        )}
      />

      <Text style={styles.sectionHeader}>Downloaded</Text>
      <FlatList
        data={downloadedModels}
        keyExtractor={(item) => item.id}
        renderItem={({ item }) => (
          <TouchableOpacity style={styles.modelRow} onPress={() => handleLoad(item)}>
            <Text style={styles.modelName}>{item.displayName}</Text>
            <Text style={styles.modelMeta}>{item.quant} · {item.capability}</Text>
          </TouchableOpacity>
        )}
        ListEmptyComponent={<Text style={styles.empty}>No models yet — search above or import a local file.</Text>}
      />

      {discoveryResults.length > 0 && (
        <>
          <Text style={styles.sectionHeader}>Search results</Text>
          <FlatList
            data={discoveryResults}
            keyExtractor={(item) => item.id}
            renderItem={({ item }) => (
              <TouchableOpacity style={styles.modelRow} onPress={() => handleDownload(item)}>
                <Text style={styles.modelName}>{item.displayName}</Text>
                <Text style={styles.modelMeta}>{item.quant} · {item.capability}</Text>
              </TouchableOpacity>
            )}
          />
        </>
      )}
    </View>
  );
}

const styles = StyleSheet.create({
  container: { flex: 1, padding: 16, gap: 12 },
  searchRow: { flexDirection: 'row', gap: 8 },
  searchInput: { flex: 1, borderWidth: 1, borderColor: '#D1D5DB', borderRadius: 8, paddingHorizontal: 12, paddingVertical: 8 },
  searchButton: { justifyContent: 'center', paddingHorizontal: 16, backgroundColor: '#2563EB', borderRadius: 8 },
  searchButtonText: { color: 'white', fontWeight: '600' },
  importButton: { borderWidth: 1, borderColor: '#2563EB', borderRadius: 8, padding: 10, alignItems: 'center' },
  importButtonText: { color: '#2563EB', fontWeight: '600' },
  sectionHeader: { fontSize: 13, fontWeight: '700', color: '#6B7280', marginTop: 4 },
  recommendedChip: { backgroundColor: '#F3F4F6', borderRadius: 8, padding: 10, marginRight: 8, minWidth: 120 },
  recommendedName: { fontWeight: '600' },
  recommendedMeta: { fontSize: 12, color: '#6B7280' },
  modelRow: { paddingVertical: 10, borderBottomWidth: 1, borderBottomColor: '#F3F4F6' },
  modelName: { fontWeight: '600' },
  modelMeta: { fontSize: 12, color: '#6B7280' },
  empty: { color: '#9CA3AF', paddingVertical: 8 },
});
