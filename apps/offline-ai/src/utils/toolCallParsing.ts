import type { ToolCall } from '../types/chat';

let callCounter = 0;
function nextCallId(): string {
  callCounter += 1;
  return `call_${Date.now()}_${callCounter}`;
}

/**
 * Larger models emit structured JSON tool calls natively through llama.rn.
 * Smaller models emit XML like <tool_call>{"name": ..., "arguments": ...}</tool_call>.
 * Supporting only one path silently drops every model that only knows the other.
 */
export function parseToolCalls(rawOutput: string): ToolCall[] {
  return [...parseJsonToolCalls(rawOutput), ...parseXmlToolCalls(rawOutput)];
}

function parseJsonToolCalls(raw: unknown): ToolCall[] {
  if (!raw || typeof raw !== 'object') return [];
  const maybeCalls = (raw as { tool_calls?: unknown }).tool_calls;
  if (!Array.isArray(maybeCalls)) return [];

  return maybeCalls
    .map((entry): ToolCall | null => {
      const fn = (entry as { function?: { name?: string; arguments?: string | Record<string, unknown> } }).function;
      if (!fn?.name) return null;
      const args = typeof fn.arguments === 'string' ? safeJsonParse(fn.arguments) : fn.arguments ?? {};
      return { id: nextCallId(), name: fn.name, arguments: args };
    })
    .filter((c): c is ToolCall => c !== null);
}

const XML_TOOL_CALL = /<tool_call>([\s\S]*?)<\/tool_call>/g;

function parseXmlToolCalls(text: string): ToolCall[] {
  const calls: ToolCall[] = [];
  for (const match of text.matchAll(XML_TOOL_CALL)) {
    const parsed = safeJsonParse(match[1].trim());
    if (parsed && typeof parsed.name === 'string') {
      calls.push({ id: nextCallId(), name: parsed.name, arguments: (parsed.arguments as Record<string, unknown>) ?? {} });
    }
  }
  return calls;
}

function safeJsonParse(text: string): Record<string, unknown> {
  try {
    return JSON.parse(text);
  } catch {
    return {};
  }
}
