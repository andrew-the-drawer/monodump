import { useCallback, useState } from 'react';
import { Image, StyleSheet, Text, TextInput, TouchableOpacity, View } from 'react-native';
import { imageGenService } from '../services/ImageGenService';
import type { ImageGenSnapshot } from '../services/ImageGenService';
import { promptEnhancementService } from '../services/PromptEnhancementService';
import { useServiceSnapshot } from '../hooks/useServiceSnapshot';

export default function ImageGenScreen() {
  const snapshot = useServiceSnapshot<ImageGenSnapshot>(
    useCallback((listener) => imageGenService.subscribe(listener), []),
    useCallback(() => imageGenService.getSnapshot(), [])
  );
  const [prompt, setPrompt] = useState('');
  const [enhance, setEnhance] = useState(true);

  const handleGenerate = async () => {
    if (!prompt.trim()) return;
    const finalPrompt = enhance ? await promptEnhancementService.enhance(prompt) : prompt;
    await imageGenService.generate(finalPrompt);
  };

  // Show a live preview every N denoising steps — without it the app looks frozen for 5-15s.
  const previewSource = snapshot.previewUri ?? snapshot.resultUri;

  return (
    <View style={styles.container}>
      <TextInput style={styles.input} value={prompt} onChangeText={setPrompt} placeholder="A dog wearing sunglasses..." multiline />

      <TouchableOpacity style={styles.toggle} onPress={() => setEnhance((v) => !v)}>
        <Text>{enhance ? '✓' : '○'} Enhance prompt with loaded LLM</Text>
      </TouchableOpacity>

      <TouchableOpacity style={styles.button} onPress={handleGenerate} disabled={snapshot.isGenerating}>
        <Text style={styles.buttonText}>{snapshot.isGenerating ? `Step ${snapshot.step}/${snapshot.totalSteps}` : 'Generate'}</Text>
      </TouchableOpacity>

      {previewSource ? (
        <Image source={{ uri: previewSource }} style={styles.preview} resizeMode="contain" />
      ) : (
        <View style={styles.placeholder}>
          <Text style={styles.placeholderText}>Preview will appear here</Text>
        </View>
      )}
    </View>
  );
}

const styles = StyleSheet.create({
  container: { flex: 1, padding: 16, gap: 12 },
  input: { borderWidth: 1, borderColor: '#D1D5DB', borderRadius: 8, padding: 12, minHeight: 60 },
  toggle: { paddingVertical: 4 },
  button: { backgroundColor: '#2563EB', borderRadius: 8, padding: 12, alignItems: 'center' },
  buttonText: { color: 'white', fontWeight: '600' },
  preview: { flex: 1, borderRadius: 8, backgroundColor: '#F3F4F6' },
  placeholder: { flex: 1, borderRadius: 8, backgroundColor: '#F3F4F6', alignItems: 'center', justifyContent: 'center' },
  placeholderText: { color: '#9CA3AF' },
});
