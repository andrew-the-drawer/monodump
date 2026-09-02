import { useEffect, useState } from 'react';
import { Alert, FlatList, ScrollView, StyleSheet, Text, TextInput, TouchableOpacity, View } from 'react-native';
import { Ionicons } from '@expo/vector-icons';
import { RECOMMENDED_MODELS } from '../types/model';
import { modelDiscoveryService } from '../services/ModelDiscoveryService';
import { modelDownloadService } from '../services/ModelDownloadService';
import { localModelImportService } from '../services/LocalModelImportService';
import { useModelStore } from '../stores/useModelStore';
import { useLlmStore } from '../stores/useLlmStore';
import { llamaService } from '../services/LlamaService';
import { Card, Chip, EmptyState, IconButton, ProgressBar, Screen, ScreenHeader, SectionLabel } from '../components/ui';
import { useTheme, radius, spacing, typography } from '../theme/theme';
import { formatBytes } from '../utils/memoryBudget';
import type { DownloadProgress, ModelCapability, ModelInfo } from '../types/model';

const CAPABILITY_ICON: Record<ModelCapability, keyof typeof Ionicons.glyphMap> = {
  text: 'chatbubble-outline',
  vision: 'eye-outline',
  code: 'code-slash-outline',
};

function useDownloadProgress(modelId: string): DownloadProgress | null {
  const [progress, setProgress] = useState<DownloadProgress | null>(null);
  useEffect(() => modelDownloadService.subscribe(modelId, setProgress), [modelId]);
  return progress;
}

export default function ModelBrowserScreen() {
  const { colors } = useTheme();
  const { downloadedModels, discoveryResults, setDiscoveryResults, addDownloadedModel, removeDownloadedModel } = useModelStore();
  const { loadedModel, setLoadedModel } = useLlmStore();
  const [query, setQuery] = useState('');
  const [isSearching, setIsSearching] = useState(false);
  const [loadingModelId, setLoadingModelId] = useState<string | null>(null);

  const runSearch = async (searchQuery: string) => {
    if (!searchQuery.trim()) return;
    setIsSearching(true);
    try {
      const results = await modelDiscoveryService.search(searchQuery, { requireFitsDevice: true });
      setDiscoveryResults(results);
    } catch (error) {
      Alert.alert('Search failed', error instanceof Error ? error.message : String(error));
    } finally {
      setIsSearching(false);
    }
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
      const downloaded = await modelDownloadService.download(model);
      addDownloadedModel(downloaded);
    } catch (error) {
      Alert.alert('Download failed', error instanceof Error ? error.message : String(error));
    }
  };

  const handleLoad = async (model: ModelInfo) => {
    setLoadingModelId(model.id);
    try {
      await llamaService.loadModel(model);
      setLoadedModel(model);
    } catch (error) {
      Alert.alert("Can't load model", error instanceof Error ? error.message : String(error));
    } finally {
      setLoadingModelId(null);
    }
  };

  const handleDelete = (model: ModelInfo) => {
    Alert.alert('Delete model', `Remove "${model.displayName}" from this device? You'll need to re-download it to use it again.`, [
      { text: 'Cancel', style: 'cancel' },
      {
        text: 'Delete',
        style: 'destructive',
        onPress: async () => {
          await modelDownloadService.deleteModel(model);
          removeDownloadedModel(model.id);
          if (loadedModel?.id === model.id) setLoadedModel(null);
        },
      },
    ]);
  };

  return (
    <Screen>
      <ScreenHeader title="Models" subtitle="Search HuggingFace, or import a .gguf file you already have" />

      <ScrollView
        contentContainerStyle={{ paddingHorizontal: spacing.lg, paddingBottom: spacing.xxxl, gap: spacing.lg }}
        keyboardShouldPersistTaps="handled"
      >
        <View style={{ gap: spacing.lg }}>
            <View style={styles.searchRow}>
              <View style={[styles.searchInputWrap, { backgroundColor: colors.surface, borderColor: colors.border }]}>
                <Ionicons name="search" size={17} color={colors.textMuted} />
                <TextInput
                  style={[styles.searchInput, { color: colors.textPrimary }]}
                  value={query}
                  onChangeText={setQuery}
                  placeholder="Search HuggingFace models..."
                  placeholderTextColor={colors.textMuted}
                  onSubmitEditing={() => runSearch(query)}
                  returnKeyType="search"
                />
              </View>
              <IconButton name="arrow-forward" onPress={() => runSearch(query)} background={colors.primary} color={colors.onPrimary} />
            </View>

            <TouchableOpacity
              onPress={handleImportLocal}
              style={[styles.importButton, { borderColor: colors.primary }]}
              activeOpacity={0.7}
            >
              <Ionicons name="folder-open-outline" size={17} color={colors.primary} />
              <Text style={[typography.subtitle, { color: colors.primary, marginLeft: spacing.sm }]}>Import a local .gguf file</Text>
            </TouchableOpacity>

            <View>
              <SectionLabel>Recommended</SectionLabel>
              <FlatList
                data={RECOMMENDED_MODELS}
                keyExtractor={(item) => item.displayName}
                horizontal
                showsHorizontalScrollIndicator={false}
                ItemSeparatorComponent={() => <View style={{ width: spacing.sm }} />}
                renderItem={({ item }) => (
                  <TouchableOpacity onPress={() => { setQuery(item.displayName); runSearch(item.displayName); }} activeOpacity={0.7}>
                    <Card style={styles.recommendedChip}>
                      <Chip label={item.capability} tone={item.capability === 'vision' ? 'vision' : 'primary'} />
                      <Text style={[typography.subtitle, { color: colors.textPrimary, marginTop: spacing.sm }]}>{item.displayName}</Text>
                      <Text style={[typography.caption, { color: colors.textMuted }]}>{item.organization}</Text>
                    </Card>
                  </TouchableOpacity>
                )}
              />
            </View>

            <View>
              <SectionLabel>Downloaded</SectionLabel>
              {downloadedModels.length === 0 ? (
                <Card>
                  <EmptyState icon="download-outline" title="No models yet" subtitle="Search above or import a local .gguf file to get started." />
                </Card>
              ) : (
                <View style={{ gap: spacing.sm }}>
                  {downloadedModels.map((item) => (
                    <ModelRow
                      key={item.id}
                      model={item}
                      isLoaded={loadedModel?.id === item.id}
                      isLoading={loadingModelId === item.id}
                      onPress={() => handleLoad(item)}
                      onDelete={() => handleDelete(item)}
                    />
                  ))}
                </View>
              )}
            </View>

            {discoveryResults.length > 0 && (
              <View>
                <SectionLabel>Search results</SectionLabel>
                <View style={{ gap: spacing.sm }}>
                  {discoveryResults.map((item) => (
                    <SearchResultRow key={item.id} model={item} onDownload={() => handleDownload(item)} />
                  ))}
                </View>
              </View>
            )}

          {isSearching && (
            <Text style={[typography.body, { color: colors.textSecondary, textAlign: 'center' }]}>Searching HuggingFace...</Text>
          )}
        </View>
      </ScrollView>
    </Screen>
  );
}

function ModelRow({
  model,
  isLoaded,
  isLoading,
  onPress,
  onDelete,
}: {
  model: ModelInfo;
  isLoaded: boolean;
  isLoading: boolean;
  onPress: () => void;
  onDelete: () => void;
}) {
  const { colors } = useTheme();
  return (
    <Card style={styles.row}>
      <TouchableOpacity onPress={onPress} disabled={isLoaded || isLoading} activeOpacity={0.7} style={[styles.row, { flex: 1 }]}>
        <View style={[styles.capabilityIcon, { backgroundColor: colors.primarySoft }]}>
          <Ionicons name={CAPABILITY_ICON[model.capability]} size={18} color={colors.primary} />
        </View>
        <View style={{ flex: 1, marginLeft: spacing.md }}>
          <Text style={[typography.subtitle, { color: colors.textPrimary }]}>{model.displayName}</Text>
          <Text style={[typography.caption, { color: colors.textMuted }]}>
            {model.organization} · {model.quant} · {formatBytes(model.file.sizeBytes)}
          </Text>
        </View>
        {isLoading ? (
          <Ionicons name="hourglass-outline" size={20} color={colors.textMuted} />
        ) : isLoaded ? (
          <View style={[styles.loadedBadge, { backgroundColor: colors.primarySoft }]}>
            <Ionicons name="checkmark" size={14} color={colors.primary} />
          </View>
        ) : (
          <Ionicons name="chevron-forward" size={18} color={colors.textMuted} />
        )}
      </TouchableOpacity>
      <TouchableOpacity onPress={onDelete} disabled={isLoading} hitSlop={8} style={{ marginLeft: spacing.sm }}>
        <Ionicons name="trash-outline" size={18} color={isLoading ? colors.textMuted : colors.danger} />
      </TouchableOpacity>
    </Card>
  );
}

function SearchResultRow({ model, onDownload }: { model: ModelInfo; onDownload: () => void }) {
  const { colors } = useTheme();
  const progress = useDownloadProgress(model.id);
  const isDownloading = progress?.status === 'downloading';

  return (
    <Card style={{ gap: spacing.sm }}>
      <View style={styles.row}>
        <View style={[styles.capabilityIcon, { backgroundColor: colors.visionSoft }]}>
          <Ionicons name={CAPABILITY_ICON[model.capability]} size={18} color={colors.vision} />
        </View>
        <View style={{ flex: 1, marginLeft: spacing.md }}>
          <Text style={[typography.subtitle, { color: colors.textPrimary }]} numberOfLines={1}>{model.displayName}</Text>
          <Text style={[typography.caption, { color: colors.textMuted }]}>
            {model.organization} · {model.quant} · {formatBytes(model.file.sizeBytes + (model.mmproj?.sizeBytes ?? 0))}
          </Text>
        </View>
        {!isDownloading && (
          <TouchableOpacity onPress={onDownload} style={[styles.downloadButton, { backgroundColor: colors.primary }]} activeOpacity={0.7}>
            <Ionicons name="download-outline" size={16} color={colors.onPrimary} />
          </TouchableOpacity>
        )}
      </View>
      {isDownloading && (
        <View style={{ gap: spacing.xs }}>
          <ProgressBar progress={progress.progress} />
          <View style={styles.row}>
            <Text style={[typography.micro, { color: colors.textMuted }]}>
              {formatBytes(progress.bytesDownloaded)} / {formatBytes(progress.totalBytes)}
            </Text>
            <TouchableOpacity onPress={() => modelDownloadService.cancel(model.id)}>
              <Text style={[typography.micro, { color: colors.danger }]}>Cancel</Text>
            </TouchableOpacity>
          </View>
        </View>
      )}
      {progress?.status === 'failed' && (
        <Text style={[typography.caption, { color: colors.danger }]}>{progress.error}</Text>
      )}
    </Card>
  );
}

const styles = StyleSheet.create({
  searchRow: { flexDirection: 'row', gap: spacing.sm, alignItems: 'center' },
  searchInputWrap: {
    flex: 1,
    flexDirection: 'row',
    alignItems: 'center',
    gap: spacing.sm,
    borderWidth: StyleSheet.hairlineWidth,
    borderRadius: radius.xl,
    paddingHorizontal: spacing.lg,
    height: 48,
  },
  searchInput: { flex: 1, fontSize: 15, height: '100%' },
  importButton: {
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'center',
    borderWidth: 1.5,
    borderRadius: radius.md,
    paddingVertical: spacing.md,
  },
  recommendedChip: { minWidth: 150, padding: spacing.md },
  row: { flexDirection: 'row', alignItems: 'center', justifyContent: 'space-between' },
  capabilityIcon: { width: 36, height: 36, borderRadius: 18, alignItems: 'center', justifyContent: 'center' },
  loadedBadge: { width: 26, height: 26, borderRadius: 13, alignItems: 'center', justifyContent: 'center' },
  downloadButton: { width: 34, height: 34, borderRadius: 17, alignItems: 'center', justifyContent: 'center' },
});
