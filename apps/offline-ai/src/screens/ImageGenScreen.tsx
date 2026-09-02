import { useEffect, useState } from 'react';
import { Alert, Image, KeyboardAvoidingView, Platform, ScrollView, StyleSheet, Text, TextInput, TouchableOpacity, View } from 'react-native';
import { Ionicons } from '@expo/vector-icons';
import { imageGenService } from '../services/ImageGenService';
import { imageModelDownloadService, type ImageDownloadProgress } from '../services/ImageModelDownloadService';
import { useServiceSnapshot } from '../hooks/useServiceSnapshot';
import { RECOMMENDED_IMAGE_MODELS, totalImageModelBytes, type ImageModelVariant } from '../types/imageModel';
import { Button, Card, EmptyState, ProgressBar, Screen, ScreenHeader, SectionLabel } from '../components/ui';
import { useTheme, radius, spacing, typography } from '../theme/theme';
import { formatBytes } from '../utils/memoryBudget';

function useDownloadProgress(variantId: string): ImageDownloadProgress | null {
  const [progress, setProgress] = useState<ImageDownloadProgress | null>(() => imageModelDownloadService.getProgress(variantId));
  useEffect(() => imageModelDownloadService.subscribe(variantId, setProgress), [variantId]);
  return progress;
}

export default function ImageGenScreen() {
  const { colors } = useTheme();

  // Hooks run unconditionally — Platform.OS is fixed for the life of the app, so this
  // doesn't change the hook count across renders, but the branch below still has to come
  // after every hook call to stay a valid Rules-of-Hooks component.
  const snapshot = useServiceSnapshot(
    (listener) => imageGenService.subscribe(listener),
    () => imageGenService.getSnapshot()
  );
  const [selectedVariant, setSelectedVariant] = useState<ImageModelVariant>(RECOMMENDED_IMAGE_MODELS[0]);
  const [prompt, setPrompt] = useState('');
  const [busyVariantId, setBusyVariantId] = useState<string | null>(null);

  if (Platform.OS !== 'ios') {
    return (
      <Screen>
        <ScreenHeader title="Image" subtitle="Generate images fully on-device" />
        <View style={{ paddingHorizontal: spacing.lg, flex: 1 }}>
          <Card>
            <EmptyState
              icon="construct-outline"
              title="iOS only, for now"
              subtitle="On-device image generation is backed by Apple's Core ML Stable Diffusion pipeline and the Neural Engine — there's no Android backend (MNN/QNN) yet. Chat, Vision, and Voice work on both platforms already."
            />
          </Card>
        </View>
      </Screen>
    );
  }

  const isLoaded = snapshot.loadedVariantId === selectedVariant.id;
  const displayUri = snapshot.previewUri ?? snapshot.resultUri;

  const handleDownload = async (variant: ImageModelVariant) => {
    setBusyVariantId(variant.id);
    try {
      await imageModelDownloadService.download(variant);
    } catch (error) {
      Alert.alert('Download failed', error instanceof Error ? error.message : String(error));
    } finally {
      setBusyVariantId(null);
    }
  };

  const handleLoad = async (variant: ImageModelVariant) => {
    setBusyVariantId(variant.id);
    try {
      const resourcesPath = imageModelDownloadService.resourcesDirectory(variant).uri.replace('file://', '');
      await imageGenService.loadModel(variant, resourcesPath);
      setSelectedVariant(variant);
    } catch (error) {
      Alert.alert("Can't load model", error instanceof Error ? error.message : String(error));
    } finally {
      setBusyVariantId(null);
    }
  };

  const handleDelete = (variant: ImageModelVariant) => {
    Alert.alert('Delete model', `Remove "${variant.displayName}" from this device?`, [
      { text: 'Cancel', style: 'cancel' },
      {
        text: 'Delete',
        style: 'destructive',
        onPress: async () => {
          if (snapshot.loadedVariantId === variant.id) imageGenService.unloadModel();
          await imageModelDownloadService.delete(variant);
        },
      },
    ]);
  };

  const handleGenerate = async () => {
    if (!prompt.trim() || !isLoaded) return;
    try {
      await imageGenService.generate(prompt.trim());
    } catch (error) {
      Alert.alert('Generation failed', error instanceof Error ? error.message : String(error));
    }
  };

  return (
    <Screen>
      <ScreenHeader title="Image" subtitle="Generate images fully on-device, via Core ML" />
      <KeyboardAvoidingView style={{ flex: 1 }} behavior="padding">
        <ScrollView contentContainerStyle={{ paddingHorizontal: spacing.lg, paddingBottom: spacing.xxxl, gap: spacing.md }} keyboardShouldPersistTaps="handled">
          <View>
            <SectionLabel>Model</SectionLabel>
            <View style={{ gap: spacing.sm }}>
              {RECOMMENDED_IMAGE_MODELS.map((variant) => (
                <VariantRow
                  key={variant.id}
                  variant={variant}
                  isSelected={selectedVariant.id === variant.id}
                  isLoaded={snapshot.loadedVariantId === variant.id}
                  isBusy={busyVariantId === variant.id}
                  onSelect={() => setSelectedVariant(variant)}
                  onDownload={() => handleDownload(variant)}
                  onLoad={() => handleLoad(variant)}
                  onDelete={() => handleDelete(variant)}
                />
              ))}
            </View>
          </View>

          <View style={styles.previewWrap}>
            {displayUri ? (
              <Image source={{ uri: displayUri }} style={styles.previewImage} resizeMode="cover" />
            ) : (
              <View style={[styles.previewPlaceholder, { borderColor: colors.border, backgroundColor: colors.surfaceAlt }]}>
                <Ionicons name="image-outline" size={28} color={colors.textMuted} />
                <Text style={[typography.caption, { color: colors.textMuted, marginTop: spacing.sm }]}>
                  {isLoaded ? 'Your generated image will appear here' : 'Load a model above to get started'}
                </Text>
              </View>
            )}
            {snapshot.isGenerating && (
              <View style={[styles.progressOverlay, { backgroundColor: colors.surface }]}>
                <ProgressBar progress={snapshot.totalSteps > 0 ? snapshot.step / snapshot.totalSteps : 0} />
                <Text style={[typography.micro, { color: colors.textMuted, marginTop: spacing.xs }]}>
                  Step {snapshot.step} / {snapshot.totalSteps}
                </Text>
              </View>
            )}
          </View>

          <TextInput
            editable={isLoaded && !snapshot.isGenerating}
            value={prompt}
            onChangeText={setPrompt}
            style={[styles.input, { borderColor: colors.border, backgroundColor: colors.surface, color: colors.textPrimary }]}
            placeholder="A dog wearing sunglasses..."
            placeholderTextColor={colors.textMuted}
            multiline
          />

          {snapshot.isGenerating ? (
            <Button label="Cancel" variant="danger" onPress={() => imageGenService.cancelGeneration()} icon="close-circle-outline" />
          ) : (
            <Button label="Generate" onPress={handleGenerate} disabled={!isLoaded || !prompt.trim()} icon="color-wand-outline" />
          )}

          {!isLoaded && (
            <Text style={[typography.caption, { color: colors.textMuted, textAlign: 'center' }]}>
              Download and load a model above before generating.
            </Text>
          )}
        </ScrollView>
      </KeyboardAvoidingView>
    </Screen>
  );
}

function VariantRow({
  variant,
  isSelected,
  isLoaded,
  isBusy,
  onSelect,
  onDownload,
  onLoad,
  onDelete,
}: {
  variant: ImageModelVariant;
  isSelected: boolean;
  isLoaded: boolean;
  isBusy: boolean;
  onSelect: () => void;
  onDownload: () => void;
  onLoad: () => void;
  onDelete: () => void;
}) {
  const { colors } = useTheme();
  const progress = useDownloadProgress(variant.id);
  const isDownloading = progress?.status === 'downloading';
  const isDownloaded = progress?.status === 'completed' || imageModelDownloadService.isDownloaded(variant);

  return (
    <TouchableOpacity onPress={onSelect} activeOpacity={0.8}>
      <Card style={{ gap: spacing.sm, borderColor: isSelected ? colors.primary : colors.border, borderWidth: isSelected ? 1.5 : StyleSheet.hairlineWidth }}>
        <View style={styles.row}>
          <View style={{ flex: 1 }}>
            <Text style={[typography.subtitle, { color: colors.textPrimary }]}>{variant.displayName}</Text>
            <Text style={[typography.caption, { color: colors.textMuted }]}>{variant.subtitle}</Text>
          </View>
          {isLoaded ? (
            <View style={[styles.loadedBadge, { backgroundColor: colors.primarySoft }]}>
              <Ionicons name="checkmark" size={14} color={colors.primary} />
            </View>
          ) : isBusy ? (
            <Ionicons name="hourglass-outline" size={20} color={colors.textMuted} />
          ) : isDownloaded ? (
            <TouchableOpacity onPress={onLoad} style={[styles.actionButton, { backgroundColor: colors.primary }]} activeOpacity={0.7}>
              <Text style={[typography.caption, { color: colors.onPrimary }]}>Load</Text>
            </TouchableOpacity>
          ) : !isDownloading ? (
            <TouchableOpacity onPress={onDownload} style={[styles.actionButton, { backgroundColor: colors.primary }]} activeOpacity={0.7}>
              <Ionicons name="download-outline" size={15} color={colors.onPrimary} />
            </TouchableOpacity>
          ) : null}
        </View>

        {isDownloading && progress ? (
          <View style={{ gap: spacing.xs }}>
            <ProgressBar progress={progress.progress} />
            <View style={styles.row}>
              <Text style={[typography.micro, { color: colors.textMuted }]}>
                {formatBytes(progress.bytesDownloaded)} / {formatBytes(progress.totalBytes)}
              </Text>
              <TouchableOpacity onPress={() => imageModelDownloadService.cancel(variant.id)}>
                <Text style={[typography.micro, { color: colors.danger }]}>Cancel</Text>
              </TouchableOpacity>
            </View>
          </View>
        ) : (
          <View style={styles.row}>
            <Text style={[typography.micro, { color: colors.textMuted }]}>{formatBytes(totalImageModelBytes(variant))}</Text>
            {isDownloaded && !isLoaded && (
              <TouchableOpacity onPress={onDelete} hitSlop={8}>
                <Text style={[typography.micro, { color: colors.danger }]}>Delete</Text>
              </TouchableOpacity>
            )}
          </View>
        )}

        {progress?.status === 'failed' && <Text style={[typography.caption, { color: colors.danger }]}>{progress.error}</Text>}
      </Card>
    </TouchableOpacity>
  );
}

const styles = StyleSheet.create({
  row: { flexDirection: 'row', alignItems: 'center', justifyContent: 'space-between' },
  loadedBadge: { width: 26, height: 26, borderRadius: 13, alignItems: 'center', justifyContent: 'center' },
  actionButton: { paddingHorizontal: spacing.md, paddingVertical: 6, borderRadius: radius.full },
  input: { borderWidth: StyleSheet.hairlineWidth, borderRadius: radius.md, padding: spacing.md, fontSize: 15, minHeight: 60 },
  previewWrap: { position: 'relative' },
  previewImage: { width: '100%', aspectRatio: 1, borderRadius: radius.lg },
  previewPlaceholder: { width: '100%', aspectRatio: 1, borderRadius: radius.lg, borderWidth: 1.5, borderStyle: 'dashed', alignItems: 'center', justifyContent: 'center' },
  progressOverlay: { position: 'absolute', left: spacing.sm, right: spacing.sm, bottom: spacing.sm, borderRadius: radius.md, padding: spacing.sm },
});
