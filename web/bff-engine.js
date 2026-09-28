// bff-engine.js — byte-exact JavaScript port of engine/tol.c (the BFF "primordial
// soup" of Agüera y Arcas et al., arXiv:2406.19108, as implemented in Google's cubff).
//
// Given the same parameters, every epoch produces exactly the same soup bytes as
// tol.c (and hence cubff). Dependency-free ES module; runs in browsers and node >= 18.
//
//   import { createSoup, loadCheckpoint, evaluate } from './bff-engine.js';
//   const soup = createSoup({ N: 16384, seed: 7 });      // bff_noheads, p = 1/4096
//   soup.runEpoch();                                     // -> ops executed this epoch
//   soup.bytes;                                          // Uint8Array(N * 64), live
//   soup.epoch;                                          // epochs done so far
//
// 64-bit arithmetic: SplitMix64 runs on (hi, lo) int32 halves in the hot loops
// (no BigInt there). BigInt is used only for a handful of per-epoch constants and
// for the reference implementation `sm64Big` used by the tests.

const T1 = 64; // program size
const T2 = 128; // tape size (two programs)
export const PROGRAM_SIZE = T1;
export const TAPE_SIZE = T2;
export const STEP_LIMIT = 8192;
const MAX_N = 1 << 20; // keeps every u64 % m below 2^53 (m <= N) and offsets < 2^32

// ---------------------------------------------------------------------------
// SplitMix64
// ---------------------------------------------------------------------------
const M64 = (1n << 64n) - 1n;
const GOLDEN = 0x9e3779b97f4a7c15n;
const GH = 0x9e3779b9, GL = 0x7f4a7c15;

/** Reference SplitMix64 on BigInt (exact, slow). */
export function sm64Big(s) {
  let z = (BigInt(s) + GOLDEN) & M64;
  z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & M64;
  z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & M64;
  return z ^ (z >> 31n);
}
/** seedf(x) = sm64(sm64(pseed) ^ sm64(x)), BigInt reference. */
export function seedfBig(pseed, x) {
  return sm64Big(sm64Big(pseed) ^ sm64Big(x));
}

// Output registers of sm64z (int32 halves of a u64).
let RH = 0, RL = 0;

// SplitMix64 finalizer on z = s + GOLDEN, given as int32 halves (zh, zl).
// Result in (RH, RL). Every 32x32 partial product is formed exactly: the low
// word with Math.imul, the high word of lo*lo with 16-bit limbs (all < 2^32).
function sm64z(zh, zl) {
  // z ^= z >> 30
  zl ^= (zl >>> 30) | (zh << 2);
  zh ^= zh >>> 30;
  // z *= 0xbf58476d1ce4e5b9
  let a0 = zl & 0xffff, a1 = zl >>> 16;
  let t = a1 * 0xe5b9 + ((a0 * 0xe5b9) >>> 16);
  let u = a0 * 0x1ce4 + (t & 0xffff);
  zh = (a1 * 0x1ce4 + (t >>> 16) + (u >>> 16) + Math.imul(zh, 0x1ce4e5b9) + Math.imul(zl, 0xbf58476d)) | 0;
  zl = Math.imul(zl, 0x1ce4e5b9);
  // z ^= z >> 27
  zl ^= (zl >>> 27) | (zh << 5);
  zh ^= zh >>> 27;
  // z *= 0x94d049bb133111eb
  a0 = zl & 0xffff; a1 = zl >>> 16;
  t = a1 * 0x11eb + ((a0 * 0x11eb) >>> 16);
  u = a0 * 0x1331 + (t & 0xffff);
  zh = (a1 * 0x1331 + (t >>> 16) + (u >>> 16) + Math.imul(zh, 0x133111eb) + Math.imul(zl, 0x94d049bb)) | 0;
  zl = Math.imul(zl, 0x133111eb);
  // z ^= z >> 31
  RL = zl ^ ((zl >>> 31) | (zh << 1));
  RH = zh ^ (zh >>> 31);
}

/**
 * Fast SplitMix64 on (hi, lo) uint32 halves; writes [hi, lo] (uint32) into `out`.
 * This is the exact code path used by the engine; exported for testing.
 */
export function sm64Pair(hi, lo, out) {
  const l = (lo >>> 0) + GL;
  sm64z((hi + GH + (l > 0xffffffff ? 1 : 0)) | 0, l | 0);
  out[0] = RH >>> 0;
  out[1] = RL >>> 0;
  return out;
}

/** u64 (hi, lo as uint32) mod m, exact for m <= 2^20. Exported for testing. */
export function modU64(hi, lo, m) {
  return (((hi >>> 0) % m) * 4294967296 + (lo >>> 0)) % m;
}

function toU64(x) {
  if (typeof x === 'bigint') return BigInt.asUintN(64, x);
  if (typeof x === 'number') {
    if (!Number.isSafeInteger(x)) throw new RangeError('seed must be a safe integer, a bigint or a decimal string');
    return BigInt.asUintN(64, BigInt(x));
  }
  if (typeof x === 'string') return BigInt.asUintN(64, BigInt(x.trim()));
  throw new TypeError('seed must be a number, bigint or string');
}
const hiOf = (b) => Number(b >> 32n) | 0;
const loOf = (b) => Number(b & 0xffffffffn); // uint32 as a (non-negative) number

// ---------------------------------------------------------------------------
// Interpreter (mirrors evaluate() in tol.c / Bff::Evaluate in cubff)
// ---------------------------------------------------------------------------
// Opcode index: 0 = no-op, 1..10 = < > { } + - . , [ ]
const OPI = new Uint8Array(256);
'<>{}+-.,[]'.split('').forEach((c, k) => { OPI[c.charCodeAt(0)] = k + 1; });

// Scratch tapes (module-level: JS is single-threaded, nothing is re-entrant).
const TAPE = new Uint8Array(T2), TAPE32 = new Int32Array(TAPE.buffer);
const REF = new Uint8Array(T2), REF32 = new Int32Array(REF.buffer);

// Plain semantics: tol.c compiled with -DNAIVE. `t` is a 128-byte tape.
function evalNaive(t, t32, stepcount, heads) {
  let pos = 0, h0 = 0, h1 = 0;
  if (heads) { h0 = t[0] & 127; h1 = t[1] & 127; pos = 2; }
  let i = 0, nskip = 0;
  for (; i < stepcount; i++) {
    h0 &= 127;
    h1 &= 127;
    switch (OPI[t[pos]]) {
      case 0: nskip++; break;
      case 1: h0--; break;
      case 2: h0++; break;
      case 3: h1--; break;
      case 4: h1++; break;
      case 5: t[h0] = t[h0] + 1; break;
      case 6: t[h0] = t[h0] - 1; break;
      case 7: t[h1] = t[h0]; break;
      case 8: t[h0] = t[h1]; break;
      case 9: // '['
        if (t[h0] === 0) {
          let d = 1;
          pos++;
          for (; pos < T2 && d > 0; pos++) {
            const c = t[pos];
            if (c === 93) d--;
            if (c === 91) d++;
          }
          pos--;
          if (d !== 0) pos = T2;
        }
        break;
      case 10: // ']'
        if (t[h0] !== 0) {
          let d = 1;
          pos--;
          for (; pos >= 0 && d > 0; pos--) {
            const c = t[pos];
            if (c === 93) d++;
            if (c === 91) d--;
          }
          pos++;
          if (d !== 0) pos = -1;
        }
        break;
    }
    if (pos < 0) { i++; break; }
    pos++;
    if (pos >= T2) { i++; break; }
  }
  return i - nskip;
}

// Same semantics plus tol.c's two exact shortcuts (its default build):
//  1. a run of k no-op bytes is consumed in one go (within the step budget);
//  2. cycle skipping: states (pos, h0, h1, tape) right after backward jumps are
//     watched with a write-free anchor and Brent's power-of-two reference; once a
//     state recurs the run is periodic and whole periods are skipped.
function evalFast(t, t32, stepcount, heads) {
  let pos = 0, h0 = 0, h1 = 0;
  if (heads) { h0 = t[0] & 127; h1 = t[1] & 127; pos = 2; }
  let i = 0, nskip = 0;
  let skipped = false, haveRef = false, refPos = 0, refH0 = 0, refH1 = 0;
  let refI = 0, refNskip = 0, power = 1, lam = 0;
  let aPos = -1, aH0 = 0, aH1 = 0, aI = 0, aNskip = 0;
  for (; i < stepcount; i++) {
    h0 &= 127;
    h1 &= 127;
    switch (OPI[t[pos]]) {
      case 0: {
        const room = stepcount - i;
        const lim = T2 - pos;
        const end = pos + (room < lim ? room : lim);
        let p = pos + 1;
        while (p < end && OPI[t[p]] === 0) p++;
        nskip += p - pos;
        i += p - pos - 1;
        pos = p - 1;
        break;
      }
      case 1: h0--; break;
      case 2: h0++; break;
      case 3: h1--; break;
      case 4: h1++; break;
      case 5: t[h0] = t[h0] + 1; aPos = -1; break;
      case 6: t[h0] = t[h0] - 1; aPos = -1; break;
      case 7: if (t[h1] !== t[h0]) { t[h1] = t[h0]; aPos = -1; } break;
      case 8: if (t[h0] !== t[h1]) { t[h0] = t[h1]; aPos = -1; } break;
      case 9: // '['
        if (t[h0] === 0) {
          let d = 1;
          pos++;
          for (; pos < T2 && d > 0; pos++) {
            const c = t[pos];
            if (c === 93) d--;
            if (c === 91) d++;
          }
          pos--;
          if (d !== 0) pos = T2;
        }
        break;
      case 10: // ']'
        if (t[h0] !== 0) {
          let d = 1;
          pos--;
          for (; pos >= 0 && d > 0; pos--) {
            const c = t[pos];
            if (c === 93) d++;
            if (c === 91) d--;
          }
          pos++;
          if (d !== 0) {
            pos = -1;
          } else if (!skipped) {
            let c = 0, cNskip = 0;
            if (aPos === pos && aH0 === h0 && aH1 === h1) {
              c = i - aI; cNskip = nskip - aNskip;
            } else if (haveRef && pos === refPos && h0 === refH0 && h1 === refH1) {
              let w = 0;
              while (w < 32 && t32[w] === REF32[w]) w++;
              if (w === 32) { c = i - refI; cNskip = nskip - refNskip; }
            }
            if (c !== 0) {
              const rem = (stepcount - 1 - i) % c;
              const cycles = (stepcount - 1 - i - rem) / c;
              nskip += cycles * cNskip;
              i = stepcount - rem - 1;
              skipped = true;
              break;
            }
            if (aPos < 0 || i - aI > 3000) {
              aPos = pos; aH0 = h0; aH1 = h1; aI = i; aNskip = nskip;
            }
            if (!haveRef || ++lam >= power) {
              if (haveRef) power <<= 1;
              lam = 0;
              haveRef = true;
              refPos = pos; refH0 = h0; refH1 = h1; refI = i; refNskip = nskip;
              for (let w = 0; w < 32; w++) REF32[w] = t32[w];
            }
          }
        }
        break;
    }
    if (pos < 0) { i++; break; }
    pos++;
    if (pos >= T2) { i++; break; }
  }
  return i - nskip;
}

/**
 * Run the BFF interpreter on a 128-byte tape in place (like tol.c's evaluate).
 * Returns the number of non-no-op instructions executed.
 * @param {Uint8Array} tape  128 bytes, modified in place
 * @param {number} [steps=8192]
 * @param {boolean|{heads?: boolean, naive?: boolean}} [opts]  heads variant / naive interpreter
 */
export function evaluate(tape, steps = STEP_LIMIT, opts = false) {
  if (!(tape instanceof Uint8Array) || tape.length !== T2) throw new TypeError('tape must be a Uint8Array(128)');
  const heads = typeof opts === 'object' && opts !== null ? !!opts.heads : !!opts;
  const naive = typeof opts === 'object' && opts !== null && !!opts.naive;
  TAPE.set(tape);
  const ops = (naive ? evalNaive : evalFast)(TAPE, TAPE32, steps >>> 0, heads);
  tape.set(TAPE);
  return ops;
}

// ---------------------------------------------------------------------------
// Soup
// ---------------------------------------------------------------------------
class Soup {
  constructor(N, bytes, epoch, opts) {
    this.N = N;
    /** The soup: N programs of 64 bytes, program p at bytes [64p, 64p+64). Live view. */
    this.bytes = bytes;
    this._w = new Int32Array(bytes.buffer, bytes.byteOffset, N * 16);
    this._perm = new Uint32Array(N);
    /** Number of epochs done; runEpoch() runs epoch index `epoch` next. */
    this.epoch = epoch;
    /** cubff "bff" variant (heads from tape[0], tape[1]) instead of bff_noheads. */
    this.heads = !!opts.heads;
    /** Use the plain interpreter (tol.c -DNAIVE); results are identical, just slower. */
    this.naive = !!opts.naive;
    this.mutProb = opts.mutProb === undefined ? 1 / 4096 : opts.mutProb;
    this.setSeed(opts.seed === undefined ? 0 : opts.seed);
  }

  /** Mutation probability per byte per interaction; stored as round(p * 2^30) like tol.c. */
  get mutProb() { return this._mutProb; }
  set mutProb(p) {
    const q = Math.round(Number(p) * (1 << 30)); // llround; p >= 0
    if (!(q >= 0 && q <= 0xffffffff)) throw new RangeError('mutProb out of range');
    this._mutProb = Number(p);
    this._mut = q;
  }
  /** Integer mutation threshold out of 2^30 (tol.c's mut_prob). */
  get mutThreshold() { return this._mut; }

  /** params.seed (u64). Changing it keeps the soup and the epoch counter (replays). */
  get seed() { return this._seed; }
  setSeed(pseed) {
    this._seed = toU64(pseed);
    const sp = sm64Big(this._seed);
    this._sph = hiOf(sp);
    this._spl = Number(sp & 0xffffffffn) | 0;
    return this;
  }

  /** Run one epoch (shuffle, pair, mutate, execute). Returns total ops executed. */
  runEpoch() {
    const N = this.N, perm = this._perm, w = this._w, epoch = this.epoch;

    // Pairing: Fisher-Yates from i = N-1 down, j = sm64(seedf(epoch*N + i)) % (i+1).
    // (i = 0 always gives j = 0, a no-op swap.)
    for (let i = 0; i < N; i++) perm[i] = i;
    const xb = BigInt.asUintN(64, BigInt(epoch) * BigInt(N) + GOLDEN);
    const xbh = hiOf(xb), xbl = loOf(xb);
    const sph = this._sph, spl = this._spl;
    for (let i = N - 1; i > 0; i--) {
      let l = xbl + i, h = xbh;
      if (l > 0xffffffff) { l -= 4294967296; h = (h + 1) | 0; }
      sm64z(h, l | 0); // sm64(epoch*N + i)
      l = ((RL ^ spl) >>> 0) + GL;
      sm64z(((RH ^ sph) + GH + (l > 0xffffffff ? 1 : 0)) | 0, l | 0); // seedf(epoch*N + i)
      l = (RL >>> 0) + GL;
      sm64z((RH + GH + (l > 0xffffffff ? 1 : 0)) | 0, l | 0); // sm64(seedf(...))
      const j = modU64(RH, RL, i + 1); // 64-bit value % (i + 1)
      const tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
    }

    // Mutation stream: rng = sm64((N*es + k)*128 + i) = sm64(128*N*es + (128k + i)).
    const es = seedfBig(this._seed, BigInt(epoch));
    const mb = BigInt.asUintN(64, 128n * BigInt(N) * es + GOLDEN);
    const mbh = hiOf(mb), mbl = loOf(mb);
    const mp = this._mut;
    const evalFn = this.naive ? evalNaive : evalFast;
    const heads = this.heads;
    const T = TAPE, T32 = TAPE32;
    const half = N >>> 1;
    let ops = 0;
    for (let k = 0; k < half; k++) {
      const a = perm[2 * k] * 16, b = perm[2 * k + 1] * 16;
      for (let q = 0; q < 16; q++) { T32[q] = w[a + q]; T32[q + 16] = w[b + q]; }
      if (mp !== 0) {
        const off = mbl + k * T2;
        for (let i = 0; i < T2; i++) {
          let l = off + i, h = mbh;
          if (l > 0xffffffff) { l -= 4294967296; h = (h + 1) | 0; }
          sm64z(h, l | 0);
          // ((rng >> 8) & (2^30 - 1)) < mut_prob
          if (((RL >>> 8) | ((RH & 0x3f) << 24)) < mp) T[i] = RL & 0xff;
        }
      }
      ops += evalFn(T, T32, STEP_LIMIT, heads);
      for (let q = 0; q < 16; q++) { w[a + q] = T32[q]; w[b + q] = T32[q + 16]; }
    }
    this.epoch = epoch + 1;
    return ops;
  }

  /** Shannon entropy (bits/byte) of the soup's byte histogram (tol.c's h0). */
  measure() {
    const counts = new Float64Array(256), bytes = this.bytes, total = bytes.length;
    for (let i = 0; i < total; i++) counts[bytes[i]]++;
    let h0 = 0;
    for (let i = 0; i < 256; i++) {
      if (counts[i]) { const f = counts[i] / total; h0 -= f * Math.log2(f); }
    }
    return h0;
  }

  /** Program p as a fresh Uint8Array(64). */
  program(p) { return this.bytes.slice(p * T1, p * T1 + T1); }

  /** Checkpoint in tol/cubff format: u64 LE {1, N, epoch} + N*64 soup bytes. */
  toCheckpoint() {
    const buf = new ArrayBuffer(24 + this.bytes.length);
    const dv = new DataView(buf);
    dv.setBigUint64(0, 1n, true);
    dv.setBigUint64(8, BigInt(this.N), true);
    dv.setBigUint64(16, BigInt(this.epoch), true);
    new Uint8Array(buf, 24).set(this.bytes);
    return buf;
  }
}

function checkN(N) {
  if (!Number.isInteger(N) || N < 2 || N > MAX_N) throw new RangeError(`N must be an integer in [2, ${MAX_N}]`);
}

/**
 * New soup initialised exactly like tol.c's init_soup (byte = sm64(64*N*s0 + 64*idx + i) % 256).
 * @param {{N: number, seed?: number|bigint|string, mutProb?: number, heads?: boolean, naive?: boolean}} o
 */
export function createSoup({ N, seed = 0, mutProb = 1 / 4096, heads = false, naive = false } = {}) {
  checkN(N);
  const soup = new Soup(N, new Uint8Array(N * T1), 0, { seed, mutProb, heads, naive });
  const s0 = seedfBig(soup.seed, 0n);
  const b = BigInt.asUintN(64, 64n * BigInt(N) * s0 + GOLDEN);
  const bh = hiOf(b), bl = loOf(b), bytes = soup.bytes, total = N * T1;
  for (let j = 0; j < total; j++) {
    let l = bl + j, h = bh;
    if (l > 0xffffffff) { l -= 4294967296; h = (h + 1) | 0; }
    sm64z(h, l | 0);
    bytes[j] = RL & 0xff;
  }
  return soup;
}

/**
 * Load a tol/cubff checkpoint (3 x u64 LE header {reset_index, N, epochs_done} + soup).
 * The soup continues at epoch = epochs_done. Seed etc. are run parameters, not stored
 * in the file: pass them here or change them later (setSeed) to replay.
 * @param {ArrayBuffer|ArrayBufferView} data
 * @param {{seed?: number|bigint|string, mutProb?: number, heads?: boolean, naive?: boolean}} [o]
 */
export function loadCheckpoint(data, { seed = 0, mutProb = 1 / 4096, heads = false, naive = false } = {}) {
  const u8 = ArrayBuffer.isView(data)
    ? new Uint8Array(data.buffer, data.byteOffset, data.byteLength)
    : new Uint8Array(data);
  if (u8.length < 24) throw new Error('bad header');
  const dv = new DataView(u8.buffer, u8.byteOffset, 24);
  const Nb = dv.getBigUint64(8, true), epochs = dv.getBigUint64(16, true);
  const N = Number(Nb);
  checkN(N);
  if (u8.length < 24 + N * T1) throw new Error('short soup');
  if (epochs > BigInt(Number.MAX_SAFE_INTEGER)) throw new RangeError('epoch counter too large');
  const bytes = new Uint8Array(N * T1);
  bytes.set(u8.subarray(24, 24 + N * T1));
  return new Soup(N, bytes, Number(epochs), { seed, mutProb, heads, naive });
}
