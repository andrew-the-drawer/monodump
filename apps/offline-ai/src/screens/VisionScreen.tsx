import { useState } from 'react';
import { Alert, Image, ScrollView, StyleSheet, Text, TextInput, TouchableOpacity, View } from 'react-native';
import * as DocumentPicker from 'expo-document-picker';
import { Ionicons } from '@expo/vector-icons';
import { llamaService } from '../services/LlamaService';
import { useLlmStore } from '../stores/useLlmStore';
import { Button, Card, EmptyState, Screen, ScreenHeader } from '../components/ui';
import { useTheme, radius, spacing, typography } from '../theme/theme';

/**
 * Vision models need a GGUF + mmproj pair, but that's a loading-time concern
 * handled transparently in LlamaService/ModelDownloadService — this screen
 * only cares that a vision-capable model is loaded.
 */
export default function VisionScreen() {
  const loadedModel = useLlmStore((s) => s.loadedModel);
  const [imageUri, setImageUri] = useState<string | null>(null);
  const [question, setQuestion] = useState('Describe this image');
  const [answer, setAnswer] = useState('');
  const [isRunning, setIsRunning] = useState(false);
  const { colors } = useTheme();

  const pickImage = async () => {
    const result = await DocumentPicker.getDocumentAsync({ type: 'image/*' });
    if (!result.canceled && result.assets[0]) {
      setImageUri(result.assets[0].uri);
      setAnswer('');
    }
  };

  const handleAsk = async () => {
    if (!imageUri || !loadedModel) return;
    setIsRunning(true);
    try {
      const { text } = await llamaService.generate({
        messages: [{ id: 'vision-question', role: 'user', content: question, createdAt: Date.now() }],
        imageUri,
      });
      setAnswer(text);
    } catch (error) {
      Alert.alert('Could not analyze image', error instanceof Error ? error.message : String(error));
    } finally {
      setIsRunning(false);
    }
  };

  if (loadedModel && loadedModel.capability !== 'vision') {
    return (
      <Screen>
        <ScreenHeader title="Vision" />
        <Card style={{ marginHorizontal: spacing.lg }}>
          <EmptyState
            icon="alert-circle-outline"
            title="No vision model loaded"
            subtitle={`"${loadedModel.displayName}" doesn't support images — load a vision model (e.g. SmolVLM) from the Models tab.`}
          />
        </Card>
      </Screen>
    );
  }

  return (
    <Screen>
      <ScreenHeader title="Vision" subtitle="Ask questions about an image, on-device" />
      <ScrollView contentContainerStyle={{ paddingHorizontal: spacing.lg, paddingBottom: spacing.xxxl, gap: spacing.md }} keyboardShouldPersistTaps="handled">
        <TouchableOpacity onPress={pickImage} activeOpacity={0.8}>
          {imageUri ? (
            <Image source={{ uri: imageUri }} style={styles.image} resizeMode="cover" />
          ) : (
            <View style={[styles.imagePicker, { borderColor: colors.border, backgroundColor: colors.surfaceAlt }]}>
              <Ionicons name="image-outline" size={28} color={colors.textMuted} />
              <Text style={[typography.body, { color: colors.textMuted, marginTop: spacing.sm }]}>Tap to pick an image</Text>
            </View>
          )}
        </TouchableOpacity>

        <TextInput
          style={[styles.input, { borderColor: colors.border, backgroundColor: colors.surface, color: colors.textPrimary }]}
          value={question}
          onChangeText={setQuestion}
          placeholder="Ask about the image..."
          placeholderTextColor={colors.textMuted}
        />

        <Button label={isRunning ? 'Thinking...' : 'Ask'} onPress={handleAsk} disabled={!imageUri || !loadedModel} loading={isRunning} icon="sparkles-outline" />

        {!loadedModel && (
          <Text style={[typography.caption, { color: colors.textMuted, textAlign: 'center' }]}>Load a vision model from the Models tab first.</Text>
        )}

        {answer ? (
          <Card>
            <Text style={[typography.body, { color: colors.textPrimary }]}>{answer}</Text>
          </Card>
        ) : null}
      </ScrollView>
    </Screen>
  );
}

const styles = StyleSheet.create({
  imagePicker: { height: 220, borderRadius: radius.lg, borderWidth: 1.5, borderStyle: 'dashed', alignItems: 'center', justifyContent: 'center' },
  image: { width: '100%', height: 220, borderRadius: radius.lg },
  input: { borderWidth: StyleSheet.hairlineWidth, borderRadius: radius.md, padding: spacing.md, fontSize: 15 },
});
