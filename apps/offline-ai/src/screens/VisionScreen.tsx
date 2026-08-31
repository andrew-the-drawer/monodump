import { useState } from 'react';
import { Image, StyleSheet, Text, TextInput, TouchableOpacity, View } from 'react-native';
import * as DocumentPicker from 'expo-document-picker';
import { llamaService } from '../services/LlamaService';
import { useLlmStore } from '../stores/useLlmStore';

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

  const pickImage = async () => {
    const result = await DocumentPicker.getDocumentAsync({ type: 'image/*' });
    if (!result.canceled && result.assets[0]) setImageUri(result.assets[0].uri);
  };

  const handleAsk = async () => {
    if (!imageUri || !loadedModel) return;
    setIsRunning(true);
    try {
      const { text } = await llamaService.generate({ prompt: question, imageUri });
      setAnswer(text);
    } finally {
      setIsRunning(false);
    }
  };

  if (loadedModel && loadedModel.capability !== 'vision') {
    return (
      <View style={styles.container}>
        <Text style={styles.warning}>Loaded model doesn't support vision. Load a vision model (e.g. SmolVLM) from the Models tab.</Text>
      </View>
    );
  }

  return (
    <View style={styles.container}>
      <TouchableOpacity style={styles.imagePicker} onPress={pickImage}>
        {imageUri ? <Image source={{ uri: imageUri }} style={styles.image} resizeMode="cover" /> : <Text>Pick an image</Text>}
      </TouchableOpacity>

      <TextInput style={styles.input} value={question} onChangeText={setQuestion} placeholder="Ask about the image..." />

      <TouchableOpacity style={styles.button} onPress={handleAsk} disabled={!imageUri || isRunning}>
        <Text style={styles.buttonText}>{isRunning ? 'Thinking...' : 'Ask'}</Text>
      </TouchableOpacity>

      {answer ? <Text style={styles.answer}>{answer}</Text> : null}
    </View>
  );
}

const styles = StyleSheet.create({
  container: { flex: 1, padding: 16, gap: 12 },
  warning: { color: '#92400E' },
  imagePicker: { height: 200, borderRadius: 8, backgroundColor: '#F3F4F6', alignItems: 'center', justifyContent: 'center', overflow: 'hidden' },
  image: { width: '100%', height: '100%' },
  input: { borderWidth: 1, borderColor: '#D1D5DB', borderRadius: 8, padding: 12 },
  button: { backgroundColor: '#2563EB', borderRadius: 8, padding: 12, alignItems: 'center' },
  buttonText: { color: 'white', fontWeight: '600' },
  answer: { fontSize: 15, color: '#111827', lineHeight: 22 },
});
