// Tiny Stack VM — a faithful interpreter of make.fun's tiny stack ISA v1.
// Runs every instance under /input/<id>/ and writes /output/<id>/stdout.bin
// and /output/<id>/exit.txt. Ported from the kit's reference VM (vm.mjs);
// where ISA.md and vm.mjs could be read two ways, vm.mjs is the rule.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const STACK_MAX = 256;
const CALLS_MAX = 64;
const MEM_WORDS = 256;
const STEP_LIMIT = 1000000;
const OUTPUT_MAX = 65536;

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const D = new Int32Array(STACK_MAX);
  const C = new Int32Array(CALLS_MAX);
  const M = new Int32Array(MEM_WORDS);
  const out = new Uint8Array(OUTPUT_MAX);
  const enc = new TextEncoder();
  const n = p.length;
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const done = (code: number): { out: Uint8Array; code: number } => ({ out: out.slice(0, olen), code });
  for (;;) {
    if (steps === STEP_LIMIT) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = p[pc];
    let imm = 0, pops = 0, pushes = 0;
    switch (op) {
      case 0x00: case 0x34: break; // HALT, RET
      case 0x30: case 0x33: imm = 2; break; // JMP, CALL
      case 0x01: imm = 1; pushes = 1; break; // PUSH8
      case 0x02: imm = 4; pushes = 1; break; // PUSH32
      case 0x52: pushes = 1; break; // IN
      case 0x03: case 0x50: case 0x51: case 0x53: pops = 1; break; // POP, PRINT, PUTC, EXIT
      case 0x17: case 0x1b: case 0x40: pops = 1; pushes = 1; break; // NEG, NOT, LOAD
      case 0x04: pops = 1; pushes = 2; break; // DUP
      case 0x41: pops = 2; break; // STORE
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: pops = 2; pushes = 1; break; // binary ops
      case 0x05: pops = 2; pushes = 2; break; // SWAP
      case 0x06: pops = 2; pushes = 3; break; // OVER
      case 0x07: pops = 3; pushes = 3; break; // ROT
      case 0x31: case 0x32: imm = 2; pops = 1; break; // JZ, JNZ
      default: return done(5); // unknown opcode
    }
    if (pc + imm >= n) return done(9); // immediate cut off by the program's end
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return done(2); // stack underflow
    if (sp - pops + pushes > STACK_MAX) return done(3); // stack overflow
    pc = next;
    switch (op) {
      case 0x00: return done(0); // HALT
      case 0x01: D[sp++] = (p[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24); break; // PUSH32
      case 0x03: sp--; break; // POP
      case 0x04: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
      case 0x06: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG, wraps at INT_MIN
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r = 0;
        switch (op) {
          case 0x10: r = (a + b) | 0; break; // ADD
          case 0x11: r = (a - b) | 0; break; // SUB
          case 0x12: r = Math.imul(a, b); break; // MUL, low 32 bits of the exact product
          case 0x13: // DIV, signed, truncated toward zero
            if (b === 0) return done(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14: // MOD, sign of a
            if (b === 0) return done(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15: // DIVU, unsigned
            if (b === 0) return done(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16: // MODU, unsigned
            if (b === 0) return done(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break; // AND
          case 0x19: r = a | b; break; // OR
          case 0x1a: r = a ^ b; break; // XOR
          case 0x1c: r = a << (b & 31); break; // SHL, only the low 5 bits count
          case 0x1d: r = a >> (b & 31); break; // SHR, arithmetic
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // SHRU, logical
          case 0x20: r = a === b ? 1 : 0; break; // EQ
          case 0x21: r = a < b ? 1 : 0; break; // LT, signed
          case 0x22: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU, unsigned
        }
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP, JZ, JNZ
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL, unsigned 16-bit target
        if (csp === CALLS_MAX) return done(7);
        C[csp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34: // RET
        if (csp === 0) return done(8);
        pc = C[--csp];
        break;
      case 0x40: { // LOAD
        const addr = D[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return done(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- ), addr is on top
        const addr = D[sp - 1];
        const v = D[sp - 2];
        if (addr < 0 || addr >= MEM_WORDS) return done(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: { // PRINT, decimal ASCII, no newline
        const bytes = enc.encode(String(D[sp - 1]));
        if (olen + bytes.length > OUTPUT_MAX) return done(11);
        sp--;
        out.set(bytes, olen);
        olen += bytes.length;
        break;
      }
      case 0x51: // PUTC, one byte
        if (olen + 1 > OUTPUT_MAX) return done(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break; // IN, -1 past the end
      case 0x53: return done(D[--sp] & 255); // EXIT, low byte
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let inp: Uint8Array;
  try {
    inp = new Uint8Array(readFileSync(join(I, id, 'input.bin')));
  } catch {
    inp = new Uint8Array(0);
  }
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
