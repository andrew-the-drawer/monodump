import type { ToolCall } from '../types/chat';

let callCounter = 0;
function nextCallId(): string {
  callCounter += 1;
  return `call_${Date.now()}_${callCounter}`;
}

export interface NativeToolCall {
  type: 'function';
  function: { name: string; arguments: string | Record<string, unknown> };
  id?: string;
}

/**
 * Larger models emit structured JSON tool calls natively through llama.rn's
 * `completion()` result (`result.tool_calls`, already parsed from the jinja
 * chat template). Smaller models that don't support that format instead emit
 * XML like <tool_call>{"name": ..., "arguments": ...}</tool_call> inline in
 * the generated text. Supporting only one path silently drops every model
 * that only knows the other.
 */
export function parseToolCalls(rawOutput: string, nativeToolCalls?: NativeToolCall[]): ToolCall[] {
  return [...parseNativeToolCalls(nativeToolCalls), ...parseXmlToolCalls(rawOutput)];
}

function parseNativeToolCalls(calls?: NativeToolCall[]): ToolCall[] {
  if (!calls) return [];
  return calls
    .filter((call) => !!call.function?.name)
    .map((call) => ({
      id: call.id ?? nextCallId(),
      name: call.function.name,
      arguments: typeof call.function.arguments === 'string' ? safeJsonParse(call.function.arguments) : call.function.arguments ?? {},
    }));
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
