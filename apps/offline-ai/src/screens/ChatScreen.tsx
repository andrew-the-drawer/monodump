import { useCallback, useState } from 'react';
import { FlatList, KeyboardAvoidingView, Platform, Pressable, StyleSheet, Text, TextInput, View } from 'react-native';
import { SafeAreaView } from 'react-native-safe-area-context';
import { Ionicons } from '@expo/vector-icons';
import { useLlmStore } from '../stores/useLlmStore';
import { useSettingsStore } from '../stores/useSettingsStore';
import { useServiceSnapshot } from '../hooks/useServiceSnapshot';
import { llamaService } from '../services/LlamaService';
import { imageGenService } from '../services/ImageGenService';
import { toolExecutorService } from '../services/ToolExecutorService';
import { promptEnhancementService } from '../services/PromptEnhancementService';
import { classifyIntentByPattern } from '../utils/intentClassifier';
import { Card, IconButton, ScreenHeader } from '../components/ui';
import { useTheme, radius, spacing, typography } from '../theme/theme';
import type { ChatMessage, ToolCall } from '../types/chat';
import type { GenerationSnapshot } from '../types/generation';

let messageCounter = 0;
function nextId(): string {
  messageCounter += 1;
  return `msg_${Date.now()}_${messageCounter}`;
}

export default function ChatScreen() {
  const { colors } = useTheme();
  const { loadedModel, messages, addMessage, updateLastMessage } = useLlmStore();
  const { intentMode, toolsEnabled, setIntentMode } = useSettingsStore();
  const generation = useServiceSnapshot<GenerationSnapshot>(
    useCallback((listener) => llamaService.subscribe(listener), []),
    useCallback(() => llamaService.getSnapshot(), [])
  );
  const [input, setInput] = useState('');

  const canUseTools = toolsEnabled && !!loadedModel?.supportsTools;

  const runToolLoop = async (conversation: ChatMessage[], toolCalls: ToolCall[]) => {
    let calls = toolCalls;
    let totalCalls = 0;
    let history = conversation;
    const tools = toolExecutorService.listToolSchemas();

    for (let iteration = 0; iteration < toolExecutorService.maxIterations && calls.length > 0; iteration += 1) {
      const results = await toolExecutorService.executeAll(calls, totalCalls);
      totalCalls += results.length;

      const toolMessages: ChatMessage[] = results.map((result) => ({
        id: nextId(),
        role: 'tool',
        content: result.error ?? result.result,
        toolResult: result,
        createdAt: Date.now(),
      }));
      toolMessages.forEach(addMessage);
      history = [...history, ...toolMessages];

      addMessage({ id: nextId(), role: 'assistant', content: '', createdAt: Date.now() });
      let streamed = '';
      const followUp = await llamaService.generate({
        messages: history,
        tools,
        onToken: (piece) => {
          streamed += piece;
          updateLastMessage(streamed);
        },
      });
      updateLastMessage(followUp.text);
      history = [...history, { id: nextId(), role: 'assistant', content: followUp.text, createdAt: Date.now() }];
      calls = followUp.toolCalls;
    }
  };

  const handleSend = async () => {
    if (!input.trim() || !loadedModel || generation.isGenerating) return;
    const text = input;
    setInput('');
    const userMessage: ChatMessage = { id: nextId(), role: 'user', content: text, createdAt: Date.now() };
    addMessage(userMessage);
    const history = [...messages, userMessage];

    const intent = intentMode === 'manual-image' ? 'image' : intentMode === 'pattern' ? classifyIntentByPattern(text) : 'text';

    if (intent === 'image') {
      const enhanced = await promptEnhancementService.enhance(text);
      const resultUri = await imageGenService.generate(enhanced);
      addMessage({ id: nextId(), role: 'assistant', content: 'Generated image', imageUri: resultUri, createdAt: Date.now() });
      return;
    }

    addMessage({ id: nextId(), role: 'assistant', content: '', createdAt: Date.now() });
    let streamed = '';
    const { text: replyText, toolCalls } = await llamaService.generate({
      messages: history,
      tools: canUseTools ? toolExecutorService.listToolSchemas() : undefined,
      onToken: (piece) => {
        streamed += piece;
        updateLastMessage(streamed);
      },
    });
    updateLastMessage(replyText);

    if (canUseTools && toolCalls.length > 0) {
      await runToolLoop([...history, { id: nextId(), role: 'assistant', content: replyText, createdAt: Date.now() }], toolCalls);
    }
  };

  return (
    <SafeAreaView style={{ flex: 1, backgroundColor: colors.background }} edges={['top', 'left', 'right', 'bottom']}>
      <KeyboardAvoidingView style={{ flex: 1 }} behavior={Platform.OS === 'ios' ? 'padding' : undefined}>
        <ScreenHeader title="Chat" subtitle={loadedModel ? loadedModel.displayName : 'No model loaded'} />

        {!loadedModel && (
          <View style={{ paddingHorizontal: spacing.lg, marginBottom: spacing.sm }}>
            <Card style={{ flexDirection: 'row', alignItems: 'center', gap: spacing.sm, backgroundColor: colors.accentSoft, borderColor: colors.accentSoft }}>
              <Ionicons name="information-circle" size={20} color={colors.accent} />
              <Text style={[typography.body, { color: colors.textPrimary, flex: 1 }]}>Pick a model from the Models tab to start chatting.</Text>
            </Card>
          </View>
        )}

        <Pressable
          onPress={() => setIntentMode(intentMode === 'manual-image' ? 'pattern' : 'manual-image')}
          style={[styles.intentRow, { borderColor: colors.border }]}
        >
          <Ionicons name="image-outline" size={16} color={intentMode === 'manual-image' ? colors.primary : colors.textSecondary} />
          <Text style={[typography.caption, { color: intentMode === 'manual-image' ? colors.primary : colors.textSecondary, flex: 1, marginLeft: spacing.xs }]}>
            Treat every message as an image request
          </Text>
          <View style={[styles.toggleTrack, { backgroundColor: intentMode === 'manual-image' ? colors.primary : colors.surfaceAlt }]}>
            <View style={[styles.toggleThumb, { alignSelf: intentMode === 'manual-image' ? 'flex-end' : 'flex-start' }]} />
          </View>
        </Pressable>

        <FlatList
          data={messages}
          keyExtractor={(item) => item.id}
          style={{ flex: 1 }}
          contentContainerStyle={{ paddingHorizontal: spacing.lg, paddingVertical: spacing.md, gap: spacing.sm }}
          renderItem={({ item }) => <MessageBubble message={item} />}
        />

        <View style={[styles.inputRow, { borderTopColor: colors.border, backgroundColor: colors.background }]}>
          <TextInput
            style={[styles.input, { backgroundColor: colors.surface, borderColor: colors.border, color: colors.textPrimary }]}
            value={input}
            onChangeText={setInput}
            placeholder="Ask something, or draw a..."
            placeholderTextColor={colors.textMuted}
            editable={!generation.isGenerating}
            multiline
          />
          <IconButton
            name={generation.isGenerating ? 'stop' : 'arrow-up'}
            onPress={generation.isGenerating ? () => llamaService.stopGeneration() : handleSend}
            background={colors.primary}
            color={colors.onPrimary}
            size={44}
            disabled={!generation.isGenerating && (!input.trim() || !loadedModel)}
          />
        </View>
      </KeyboardAvoidingView>
    </SafeAreaView>
  );
}

function MessageBubble({ message }: { message: ChatMessage }) {
  const { colors } = useTheme();

  if (message.role === 'tool') {
    return (
      <View style={[styles.toolBubble, { backgroundColor: colors.surfaceAlt, borderColor: colors.border }]}>
        <Ionicons name="construct-outline" size={14} color={colors.textMuted} />
        <Text style={[typography.micro, { color: colors.textMuted, marginLeft: spacing.xs, flex: 1 }]} numberOfLines={3}>
          {message.toolResult?.name}: {message.content}
        </Text>
      </View>
    );
  }

  const isUser = message.role === 'user';
  return (
    <View style={[styles.bubbleRow, { justifyContent: isUser ? 'flex-end' : 'flex-start' }]}>
      <View
        style={[
          styles.bubble,
          isUser
            ? { backgroundColor: colors.primary, borderBottomRightRadius: 4 }
            : { backgroundColor: colors.surface, borderColor: colors.border, borderWidth: StyleSheet.hairlineWidth, borderBottomLeftRadius: 4 },
        ]}
      >
        <Text style={[typography.body, { color: isUser ? colors.onPrimary : colors.textPrimary }]}>{message.content || '…'}</Text>
      </View>
    </View>
  );
}

const styles = StyleSheet.create({
  intentRow: {
    flexDirection: 'row',
    alignItems: 'center',
    marginHorizontal: spacing.lg,
    marginBottom: spacing.sm,
    paddingVertical: spacing.sm,
    paddingHorizontal: spacing.md,
    borderRadius: radius.md,
    borderWidth: StyleSheet.hairlineWidth,
  },
  toggleTrack: { width: 36, height: 20, borderRadius: 10, padding: 2, justifyContent: 'center' },
  toggleThumb: { width: 16, height: 16, borderRadius: 8, backgroundColor: '#FFFFFF' },
  bubbleRow: { flexDirection: 'row' },
  bubble: { maxWidth: '82%', paddingHorizontal: 14, paddingVertical: 10, borderRadius: 18 },
  toolBubble: {
    flexDirection: 'row',
    alignItems: 'center',
    alignSelf: 'flex-start',
    maxWidth: '90%',
    paddingHorizontal: 12,
    paddingVertical: 8,
    borderRadius: radius.md,
    borderWidth: StyleSheet.hairlineWidth,
  },
  inputRow: {
    flexDirection: 'row',
    alignItems: 'flex-end',
    gap: spacing.sm,
    paddingHorizontal: spacing.lg,
    paddingTop: spacing.sm,
    paddingBottom: spacing.md,
    borderTopWidth: StyleSheet.hairlineWidth,
  },
  input: {
    flex: 1,
    borderWidth: StyleSheet.hairlineWidth,
    borderRadius: radius.xl,
    paddingHorizontal: spacing.lg,
    paddingVertical: 12,
    maxHeight: 120,
    fontSize: 15,
  },
});
