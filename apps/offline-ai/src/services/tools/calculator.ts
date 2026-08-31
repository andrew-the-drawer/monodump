/**
 * Recursive descent parser for basic arithmetic. Never eval() — the input
 * comes from model-generated tool-call arguments, i.e. untrusted text.
 */

type TokenType = 'number' | 'operator' | 'lparen' | 'rparen' | 'eof';

interface Token {
  type: TokenType;
  value: string;
}

function tokenize(expression: string): Token[] {
  const tokens: Token[] = [];
  let i = 0;

  while (i < expression.length) {
    const ch = expression[i];

    if (/\s/.test(ch)) {
      i += 1;
      continue;
    }
    if (/[0-9.]/.test(ch)) {
      let num = '';
      while (i < expression.length && /[0-9.]/.test(expression[i])) {
        num += expression[i];
        i += 1;
      }
      tokens.push({ type: 'number', value: num });
      continue;
    }
    if ('+-*/^'.includes(ch)) {
      tokens.push({ type: 'operator', value: ch });
      i += 1;
      continue;
    }
    if (ch === '(') {
      tokens.push({ type: 'lparen', value: ch });
      i += 1;
      continue;
    }
    if (ch === ')') {
      tokens.push({ type: 'rparen', value: ch });
      i += 1;
      continue;
    }
    throw new Error(`Unexpected character '${ch}' at position ${i}`);
  }

  tokens.push({ type: 'eof', value: '' });
  return tokens;
}

class Parser {
  private pos = 0;
  constructor(private tokens: Token[]) {}

  private peek(): Token {
    return this.tokens[this.pos];
  }

  private consume(type: TokenType): Token {
    const token = this.peek();
    if (token.type !== type) {
      throw new Error(`Expected ${type} but got ${token.type} ('${token.value}')`);
    }
    this.pos += 1;
    return token;
  }

  // expression := term (('+' | '-') term)*
  parseExpression(): number {
    let value = this.parseTerm();
    while (this.peek().type === 'operator' && (this.peek().value === '+' || this.peek().value === '-')) {
      const op = this.consume('operator').value;
      const rhs = this.parseTerm();
      value = op === '+' ? value + rhs : value - rhs;
    }
    return value;
  }

  // term := factor (('*' | '/') factor)*
  private parseTerm(): number {
    let value = this.parseFactor();
    while (this.peek().type === 'operator' && (this.peek().value === '*' || this.peek().value === '/')) {
      const op = this.consume('operator').value;
      const rhs = this.parseFactor();
      if (op === '/' && rhs === 0) throw new Error('Division by zero');
      value = op === '*' ? value * rhs : value / rhs;
    }
    return value;
  }

  // factor := power (('^') power)*
  private parseFactor(): number {
    let value = this.parsePower();
    while (this.peek().type === 'operator' && this.peek().value === '^') {
      this.consume('operator');
      const rhs = this.parsePower();
      value **= rhs;
    }
    return value;
  }

  // power := ('-')? (number | '(' expression ')')
  private parsePower(): number {
    if (this.peek().type === 'operator' && this.peek().value === '-') {
      this.consume('operator');
      return -this.parsePower();
    }
    if (this.peek().type === 'lparen') {
      this.consume('lparen');
      const value = this.parseExpression();
      this.consume('rparen');
      return value;
    }
    const token = this.consume('number');
    return Number(token.value);
  }
}

export function evaluateExpression(expression: string): number {
  const parser = new Parser(tokenize(expression));
  const result = parser.parseExpression();
  if (!Number.isFinite(result)) throw new Error('Result is not a finite number');
  return result;
}

export const calculatorTool = {
  name: 'calculator',
  description: 'Evaluate a basic arithmetic expression (+ - * / ^ and parentheses).',
  parameters: {
    type: 'object',
    properties: { expression: { type: 'string', description: 'e.g. "(2 + 3) * 4"' } },
    required: ['expression'],
  },
  execute: async (args: Record<string, unknown>): Promise<string> => {
    const expression = String(args.expression ?? '');
    return String(evaluateExpression(expression));
  },
};
