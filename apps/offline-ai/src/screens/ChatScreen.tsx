import { useCallback, useState } from 'react';
import { FlatList, KeyboardAvoidingView, Platform, StyleSheet, Switch, Text, TextInput, TouchableOpacity, View } from 'react-native';
import { useLlmStore } from '../stores/useLlmStore';
import { useSettingsStore } from '../stores/useSettingsStore';
import { useServiceSnapshot } from '../hooks/useServiceSnapshot';
import { llamaService } from '../services/LlamaService';
import { imageGenService } from '../services/ImageGenService';
import { toolExecutorService } from '../services/ToolExecutorService';
import { promptEnhancementService } from '../services/PromptEnhancementService';
import { classifyIntentByPattern } from '../utils/intentClassifier';
import type { ChatMessage, ToolCall } from '../types/chat';
import type { GenerationSnapshot } from '../types/generation';

let messageCounter = 0;
function nextId(): string {
  messageCounter += 1;
  return `msg_${Date.now()}_${messageCounter}`;
}

export default function ChatScreen() {
  const { loadedModel, messages, addMessage, updateLastMessage } = useLlmStore();
  const { intentMode, toolsEnabled, setIntentMode } = useSettingsStore();
  const generation = useServiceSnapshot<GenerationSnapshot>(
    useCallback((listener) => llamaService.subscribe(listener), []),
    useCallback(() => llamaService.getSnapshot(), [])
  );
  const [input, setInput] = useState('');

  const runToolLoop = async (toolCalls: ToolCall[]) => {
    let calls = toolCalls;
    let totalCalls = 0;
    for (let iteration = 0; iteration < toolExecutorService.maxIterations && calls.length > 0; iteration += 1) {
      const results = await toolExecutorService.executeAll(calls, totalCalls);
      totalCalls += results.length;
      for (const result of results) {
        addMessage({ id: nextId(), role: 'tool', content: result.error ?? result.result, toolResult: result, createdAt: Date.now() });
      }
      const followUp = await llamaService.generate({ prompt: '' });
      calls = followUp.toolCalls;
      if (followUp.text) addMessage({ id: nextId(), role: 'assistant', content: followUp.text, createdAt: Date.now() });
    }
  };

  const handleSend = async () => {
    if (!input.trim() || !loadedModel) return;
    const text = input;
    setInput('');
    addMessage({ id: nextId(), role: 'user', content: text, createdAt: Date.now() });

    const intent = intentMode === 'manual-image' ? 'image' : intentMode === 'pattern' ? classifyIntentByPattern(text) : 'text';

    if (intent === 'image') {
      const enhanced = await promptEnhancementService.enhance(text);
      const resultUri = await imageGenService.generate(enhanced);
      addMessage({ id: nextId(), role: 'assistant', content: 'Generated image', imageUri: resultUri, createdAt: Date.now() });
      return;
    }

    addMessage({ id: nextId(), role: 'assistant', content: '', createdAt: Date.now() });
    const { text: reply, toolCalls } = await llamaService.generate({
      prompt: text,
      onToken: (piece) => updateLastMessage(generation.streamingText + piece),
    });
    updateLastMessage(reply);

    if (toolsEnabled && loadedModel.supportsTools && toolCalls.length > 0) {
      await runToolLoop(toolCalls);
    }
  };

  return (
    <KeyboardAvoidingView style={styles.container} behavior={Platform.OS === 'ios' ? 'padding' : undefined}>
      {!loadedModel && (
        <View style={styles.banner}>
          <Text style={styles.bannerText}>No model loaded. Pick one from the Models tab.</Text>
        </View>
      )}

      <View style={styles.intentRow}>
        <Text style={styles.intentLabel}>Manual image override</Text>
        <Switch
          value={intentMode === 'manual-image'}
          onValueChange={(value) => setIntentMode(value ? 'manual-image' : 'pattern')}
        />
      </View>

      <FlatList
        data={messages}
        keyExtractor={(item) => item.id}
        style={styles.list}
        renderItem={({ item }) => <MessageBubble message={item} />}
      />

      <View style={styles.inputRow}>
        <TextInput
          style={styles.input}
          value={input}
          onChangeText={setInput}
          placeholder="Ask something, or 'draw a...' for images"
          editable={!generation.isGenerating}
        />
        <TouchableOpacity style={styles.sendButton} onPress={handleSend} disabled={generation.isGenerating}>
          <Text style={styles.sendButtonText}>{generation.isGenerating ? '...' : 'Send'}</Text>
        </TouchableOpacity>
      </View>
    </KeyboardAvoidingView>
  );
}

function MessageBubble({ message }: { message: ChatMessage }) {
  return (
    <View style={[styles.bubble, message.role === 'user' ? styles.bubbleUser : styles.bubbleOther]}>
      <Text style={styles.bubbleRole}>{message.role}</Text>
      <Text>{message.content}</Text>
    </View>
  );
}

const styles = StyleSheet.create({
  container: { flex: 1 },
  banner: { backgroundColor: '#FEF3C7', padding: 8 },
  bannerText: { color: '#92400E', fontSize: 13 },
  intentRow: { flexDirection: 'row', justifyContent: 'space-between', alignItems: 'center', padding: 8 },
  intentLabel: { fontSize: 13, color: '#374151' },
  list: { flex: 1, paddingHorizontal: 12 },
  bubble: { padding: 10, borderRadius: 8, marginVertical: 4, maxWidth: '85%' },
  bubbleUser: { backgroundColor: '#DBEAFE', alignSelf: 'flex-end' },
  bubbleOther: { backgroundColor: '#F3F4F6', alignSelf: 'flex-start' },
  bubbleRole: { fontSize: 10, color: '#6B7280', marginBottom: 2 },
  inputRow: { flexDirection: 'row', padding: 8, gap: 8 },
  input: { flex: 1, borderWidth: 1, borderColor: '#D1D5DB', borderRadius: 8, paddingHorizontal: 12, paddingVertical: 8 },
  sendButton: { justifyContent: 'center', paddingHorizontal: 16, backgroundColor: '#2563EB', borderRadius: 8 },
  sendButtonText: { color: 'white', fontWeight: '600' },
});
