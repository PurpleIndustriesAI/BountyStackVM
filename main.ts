import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

type Result = { out: number[]; code: number };

function execute(program: Uint8Array, input: Uint8Array): Result {
  const data = new Int32Array(256);
  const calls = new Uint32Array(64);
  const memory = new Int32Array(256);
  const out: number[] = [];
  let sp = 0;
  let cp = 0;
  let pc = 0;
  let ip = 0;
  let steps = 0;
  const fault = (code: number): Result => ({ out, code });
  const underflow = (count: number): boolean => sp < count;
  const overflow = (count: number): boolean => sp + count > 256;

  for (;;) {
    if (steps >= 1_000_000) return fault(10);
    if (pc < 0 || pc >= program.length) return fault(9);
    const op = program[pc++];
    const immediate = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    const known = op <= 7 || (op >= 0x10 && op <= 0x1e) || (op >= 0x20 && op <= 0x22) || (op >= 0x30 && op <= 0x34) || (op >= 0x40 && op <= 0x41) || (op >= 0x50 && op <= 0x53);
    if (!known) return fault(5);
    if (pc + immediate > program.length) return fault(9);
    steps++;

    if (op === 0) return fault(0);
    if (op === 1) {
      if (overflow(1)) return fault(3);
      data[sp++] = program[pc++] << 24 >> 24;
    } else if (op === 2) {
      if (overflow(1)) return fault(3);
      data[sp++] = program[pc] | program[pc + 1] << 8 | program[pc + 2] << 16 | program[pc + 3] << 24;
      pc += 4;
    } else if (op >= 0x10 && op <= 0x1e && op !== 0x17 && op !== 0x1b) {
      if (underflow(2)) return fault(2);
      const b = data[--sp];
      const a = data[--sp];
      let value: number;
      if (op === 0x10) value = a + b;
      else if (op === 0x11) value = a - b;
      else if (op === 0x12) value = Math.imul(a, b);
      else if (op === 0x13 || op === 0x14) {
        if (b === 0) return fault(4);
        value = op === 0x13 ? Math.trunc(a / b) : a % b;
      } else if (op === 0x15 || op === 0x16) {
        if (b === 0) return fault(4);
        value = op === 0x15 ? Math.floor((a >>> 0) / (b >>> 0)) : (a >>> 0) % (b >>> 0);
      } else if (op === 0x18) value = a & b;
      else if (op === 0x19) value = a | b;
      else if (op === 0x1a) value = a ^ b;
      else if (op === 0x1c) value = a << b;
      else if (op === 0x1d) value = a >> b;
      else value = a >>> b;
      data[sp++] = value;
    } else if (op === 0x17 || op === 0x1b) {
      if (underflow(1)) return fault(2);
      data[sp - 1] = op === 0x17 ? -data[sp - 1] : ~data[sp - 1];
    } else if (op === 0x20 || op === 0x21 || op === 0x22) {
      if (underflow(2)) return fault(2);
      const b = data[--sp];
      const a = data[--sp];
      data[sp++] = (op === 0x20 ? a === b : op === 0x21 ? a < b : (a >>> 0) < (b >>> 0)) ? 1 : 0;
    } else if (op >= 0x30 && op <= 0x32) {
      if (op !== 0x30 && underflow(1)) return fault(2);
      const relative = (program[pc] | program[pc + 1] << 8) << 16 >> 16;
      pc += 2;
      const take = op === 0x30 || (op === 0x31 ? data[--sp] === 0 : data[--sp] !== 0);
      if (take) pc += relative;
    } else if (op === 0x33) {
      if (cp >= 64) return fault(7);
      const target = program[pc] | program[pc + 1] << 8;
      pc += 2;
      calls[cp++] = pc;
      pc = target;
    } else if (op === 0x34) {
      if (cp === 0) return fault(8);
      pc = calls[--cp];
    } else if (op === 0x40) {
      if (underflow(1)) return fault(2);
      const address = data[sp - 1];
      if (address < 0 || address > 255) return fault(6);
      data[sp - 1] = memory[address];
    } else if (op === 0x41) {
      if (underflow(2)) return fault(2);
      const address = data[--sp];
      const value = data[--sp];
      if (address < 0 || address > 255) return fault(6);
      memory[address] = value;
    } else if (op === 0x50) {
      if (underflow(1)) return fault(2);
      const text = String(data[--sp]);
      if (out.length + text.length > 65536) return fault(11);
      for (let i = 0; i < text.length; i++) out.push(text.charCodeAt(i));
    } else if (op === 0x51) {
      if (underflow(1)) return fault(2);
      if (out.length >= 65536) return fault(11);
      out.push(data[--sp] & 255);
    } else if (op === 0x52) {
      if (overflow(1)) return fault(3);
      data[sp++] = ip < input.length ? input[ip++] : -1;
    } else if (op === 0x53) {
      if (underflow(1)) return fault(2);
      return fault(data[--sp] & 255);
    } else if (op === 3) {
      if (underflow(1)) return fault(2);
      sp--;
    } else if (op === 4) {
      if (underflow(1)) return fault(2);
      if (overflow(1)) return fault(3);
      data[sp] = data[sp - 1];
      sp++;
    } else if (op === 5) {
      if (underflow(2)) return fault(2);
      const value = data[sp - 1];
      data[sp - 1] = data[sp - 2];
      data[sp - 2] = value;
    } else if (op === 6) {
      if (underflow(2)) return fault(2);
      if (overflow(1)) return fault(3);
      data[sp] = data[sp - 2];
      sp++;
    } else if (op === 7) {
      if (underflow(3)) return fault(2);
      const a = data[sp - 3];
      data[sp - 3] = data[sp - 2];
      data[sp - 2] = data[sp - 1];
      data[sp - 1] = a;
    }
  }
}

const inputRoot = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputRoot = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(inputRoot).sort()) {
  const result = execute(new Uint8Array(readFileSync(join(inputRoot, id, 'program.bin'))), new Uint8Array(readFileSync(join(inputRoot, id, 'input.bin'))));
  mkdirSync(join(outputRoot, id), { recursive: true });
  writeFileSync(join(outputRoot, id, 'stdout.bin'), Uint8Array.from(result.out));
  writeFileSync(join(outputRoot, id, 'exit.txt'), `${result.code}\n`);
}
