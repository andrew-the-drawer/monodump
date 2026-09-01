import type { ToolCall, ToolResult } from '../types/chat';
import type { ToolDefinitionSchema } from './LlamaService';
import { calculatorTool } from './tools/calculator';
import { dateTimeTool } from './tools/dateTime';
import { deviceInfoTool } from './tools/deviceInfo';
import { webSearchTool } from './tools/webSearch';

export interface ToolDefinition {
  name: string;
  description: string;
  parameters: Record<string, unknown>;
  execute: (args: Record<string, unknown>) => Promise<string>;
}

const MAX_ITERATIONS = 3;
const MAX_TOTAL_CALLS = 5;

/**
 * Runs the generate -> parse tool calls -> execute -> inject results -> generate
 * loop described in the article. Capped so a confused model can't loop forever.
 */
class ToolExecutorService {
  private registry = new Map<string, ToolDefinition>();

  constructor() {
    for (const tool of [calculatorTool, dateTimeTool, deviceInfoTool, webSearchTool]) {
      this.registry.set(tool.name, tool);
    }
  }

  listTools(): ToolDefinition[] {
    return [...this.registry.values()];
  }

  /** OpenAI-style tool schema for llama.rn's jinja-templated `tools` param. */
  listToolSchemas(): ToolDefinitionSchema[] {
    return this.listTools().map((tool) => ({
      type: 'function',
      function: { name: tool.name, description: tool.description, parameters: tool.parameters },
    }));
  }

  get maxIterations(): number {
    return MAX_ITERATIONS;
  }

  get maxTotalCalls(): number {
    return MAX_TOTAL_CALLS;
  }

  async execute(call: ToolCall): Promise<ToolResult> {
    const tool = this.registry.get(call.name);
    if (!tool) {
      return { toolCallId: call.id, name: call.name, result: '', error: `Unknown tool: ${call.name}` };
    }
    try {
      const result = await tool.execute(call.arguments);
      return { toolCallId: call.id, name: call.name, result };
    } catch (error) {
      return { toolCallId: call.id, name: call.name, result: '', error: error instanceof Error ? error.message : String(error) };
    }
  }

  async executeAll(calls: ToolCall[], totalCallsSoFar: number): Promise<ToolResult[]> {
    const budget = Math.max(0, MAX_TOTAL_CALLS - totalCallsSoFar);
    const results: ToolResult[] = [];
    for (const call of calls.slice(0, budget)) {
      results.push(await this.execute(call));
    }
    return results;
  }
}

export const toolExecutorService = new ToolExecutorService();
