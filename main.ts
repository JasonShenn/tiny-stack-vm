// Tiny stack VM: implements generator/subject/ISA.md (vm.mjs is the rule).
// Usage: node main.ts — reads /input/<id>/{program,input}.bin, writes
// /output/<id>/{stdout.bin,exit.txt}. Env MAKEFUN_INPUT_DIR / MAKEFUN_OUTPUT_DIR override.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Named limits (values unchanged from the original magic numbers).
const MAX_STEPS = 1000000;
const STACK_CAP = 256;
const OUT_CAP = 65536;

function run(p: Uint8Array, q: Uint8Array): { o: Uint8Array; c: number } {
  const D = new Int32Array(STACK_CAP), C = new Int32Array(64), M = new Int32Array(STACK_CAP);
  const O = new Uint8Array(OUT_CAP);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, st = 0, tc = 0;
  const trap = (c: number) => ({ o: O.slice(0, ol), c });
  const chk = (a: number, b: number): boolean => {
    tc = sp < a ? 2 : sp - a + b > STACK_CAP ? 3 : 0;
    return tc !== 0;
  };
  for (;;) {
    if (st === MAX_STEPS) return trap(10);
    if (pc < 0 || pc >= p.length) return trap(9);
    const op = p[pc];
    const ok = op <= 7 || (op >= 0x10 && op <= 0x22) || (op >= 0x30 && op <= 0x34)
      || op === 0x40 || op === 0x41 || (op >= 0x50 && op <= 0x53);
    if (!ok) return trap(5);
    const im = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    if (pc + im >= p.length) return trap(9);
    st++;
    const nx = pc + 1 + im;
    pc = nx;
    switch (op) {
      case 0x00: return { o: O.slice(0, ol), c: 0 };
      case 0x01:
        if (chk(0, 1)) return trap(tc);
        D[sp++] = (p[nx - 1] << 24) >> 24;
        break;
      case 0x02:
        if (chk(0, 1)) return trap(tc);
        D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
        break;
      case 0x03:
        if (chk(1, 0)) return trap(tc);
        sp--;
        break;
      case 0x04:
        if (chk(1, 2)) return trap(tc);
        D[sp] = D[sp - 1]; sp++;
        break;
      case 0x05: {
        if (chk(2, 2)) return trap(tc);
        const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t;
        break;
      }
      case 0x06:
        if (chk(2, 3)) return trap(tc);
        D[sp] = D[sp - 2]; sp++;
        break;
      case 0x07: {
        if (chk(3, 3)) return trap(tc);
        const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a;
        break;
      }
      case 0x17:
        if (chk(1, 1)) return trap(tc);
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 0x1b:
        if (chk(1, 1)) return trap(tc);
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        if (chk(2, 1)) return trap(tc);
        const b = D[sp - 1], a = D[sp - 2];
        let r = 0;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return trap(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return trap(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return trap(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return trap(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2; D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        if (op !== 0x30) {
          if (chk(1, 0)) return trap(tc);
          const v = D[--sp];
          if ((op === 0x31) !== (v === 0)) break;
        }
        pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return trap(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return trap(8);
        pc = C[--cp];
        break;
      case 0x40: {
        if (chk(1, 1)) return trap(tc);
        const a = D[sp - 1];
        if (a < 0 || a > 255) return trap(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: {
        if (chk(2, 0)) return trap(tc);
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a > 255) return trap(6);
        sp -= 2; M[a] = v;
        break;
      }
      case 0x50: {
        if (chk(1, 0)) return trap(tc);
        const t = String(D[sp - 1]);
        if (ol + t.length > OUT_CAP) return trap(11);
        sp--;
        for (let i = 0; i < t.length; i++) O[ol++] = t.charCodeAt(i);
        break;
      }
      case 0x51:
        if (chk(1, 0)) return trap(tc);
        if (ol + 1 > OUT_CAP) return trap(11);
        O[ol++] = D[--sp] & 255;
        break;
      case 0x52:
        if (chk(0, 1)) return trap(tc);
        D[sp++] = ip < q.length ? q[ip++] : -1;
        break;
      case 0x53:
        if (chk(1, 0)) return trap(tc);
        return { o: O.slice(0, ol), c: D[--sp] & 255 };
      default:
        return trap(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let p: Uint8Array, q: Uint8Array;
  try { p = readFileSync(join(I, id, 'program.bin')); } catch { p = new Uint8Array(0); }
  try { q = readFileSync(join(I, id, 'input.bin')); } catch { q = new Uint8Array(0); }
  const r = run(p, q);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), `${r.c}\n`);
}
