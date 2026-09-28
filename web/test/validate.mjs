#!/usr/bin/env node
// Byte-exactness validation of web/bff-engine.js against engine/tol.c.
//
//   node web/test/validate.mjs            # everything (a few minutes)
//   node web/test/validate.mjs --quick    # skip the naive-JS runs of the soup cases
//   node web/test/validate.mjs --no-bench # skip the speed benchmark
//   TOL=/path/to/tol  CC=clang  BROTLI_PREFIX=/opt/homebrew/opt/brotli   (optional)
//
// tol is built (if missing or older than tol.c) with
//   cc -O3 -I$BROTLI/include engine/tol.c -L$BROTLI/lib -lbrotlienc -lm -o /tmp/tol_local
// Every checkpoint file tol writes must be byte-identical (header + soup) to the
// JS soup's toCheckpoint() after the same number of epochs, for both JS interpreters
// (fast = tol default build, naive = tol -DNAIVE).

import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { webcrypto } from 'node:crypto';

// BFF_ENGINE=/path/to/engine.js tests another copy of the engine (used for negative controls).
const {
  createSoup, loadCheckpoint, evaluate, sm64Big, seedfBig, sm64Pair, modU64,
} = await import(process.env.BFF_ENGINE ? pathToFileURL(path.resolve(process.env.BFF_ENGINE)).href : '../bff-engine.js');

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const TOL_C = path.join(ROOT, 'engine', 'tol.c');
const ARGV = process.argv.slice(2);
const ARGS = new Set(ARGV);
const QUICK = ARGS.has('--quick');
const KEEP = ARGS.has('--keep');
// --only PREFIX: run only the soup cases whose name starts with PREFIX (skips sections 1, 2, 4).
const ONLY = ARGS.has('--only') ? ARGV[ARGV.indexOf('--only') + 1] : null;
const BENCH = !ARGS.has('--no-bench') && !ONLY;
const WORK = fs.mkdtempSync(path.join(os.tmpdir(), 'bff-validate-'));

let failures = 0;
function report(ok, name, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? '  (' + detail + ')' : ''}`);
  if (!ok) failures++;
}
const pad10 = (e) => String(e).padStart(10, '0');
const now = () => performance.now();

// ---------------------------------------------------------------------------
// Build tol and an evaluate() harness
// ---------------------------------------------------------------------------
function brotliPrefix() {
  if (process.env.BROTLI_PREFIX) return process.env.BROTLI_PREFIX;
  for (const p of ['/opt/homebrew/opt/brotli', '/usr/local/opt/brotli']) if (fs.existsSync(p)) return p;
  try { return execFileSync('brew', ['--prefix', 'brotli'], { encoding: 'utf8' }).trim(); } catch { return '/usr'; }
}
const CC = process.env.CC || 'cc'; // execFile does not see shell aliases
const BR = brotliPrefix();
function compile(src, out, extra = []) {
  execFileSync(CC, ['-O3', ...extra, `-I${BR}/include`, `-I${path.dirname(TOL_C)}`, src,
    `-L${BR}/lib`, '-lbrotlienc', '-lm', '-o', out], { stdio: ['ignore', 'ignore', 'inherit'] });
}
const TOL = process.env.TOL || '/tmp/tol_local';
if (!fs.existsSync(TOL) || fs.statSync(TOL).mtimeMs < fs.statSync(TOL_C).mtimeMs) {
  console.log(`building ${TOL}`);
  compile(TOL_C, TOL);
}
const HARNESS_C = path.join(WORK, 'eval_harness.c');
fs.writeFileSync(HARNESS_C, `
#define main tol_main
#include "tol.c"
#undef main
// stdin: 128-byte tapes; stdout: tape after evaluate() + u32 ops.  argv: heads steps
int main(int argc, char **argv) {
  g_heads = atoi(argv[1]);
  uint32_t steps = (uint32_t)strtoul(argv[2], 0, 10);
  uint8_t tape[T2];
  while (fread(tape, 1, T2, stdin) == T2) {
    uint32_t ops = evaluate(tape, steps);
    fwrite(tape, 1, T2, stdout); fwrite(&ops, 4, 1, stdout);
  }
  return 0;
}
`);
const H_FAST = path.join(WORK, 'harness_fast'), H_NAIVE = path.join(WORK, 'harness_naive');
compile(HARNESS_C, H_FAST, ['-w']);
compile(HARNESS_C, H_NAIVE, ['-w', '-DNAIVE']);
console.log(`tol: ${TOL}   work dir: ${WORK}\n`);

// ---------------------------------------------------------------------------
// 1. SplitMix64 and u64 helpers vs BigInt
// ---------------------------------------------------------------------------
function randU32s(n) {
  const a = new Uint32Array(n);
  for (let i = 0; i < n; i += 16384) webcrypto.getRandomValues(a.subarray(i, Math.min(n, i + 16384)));
  return a;
}
if (!ONLY) {
  const M = 1_000_000;
  const r = randU32s(2 * M);
  const edges = [0n, 1n, 0xffffffffn, 0x100000000n, 0x7fffffffffffffffn, 0x8000000000000000n,
    (1n << 64n) - 1n, (1n << 64n) - 0x9e3779b97f4a7c15n, (1n << 64n) - 0x9e3779b97f4a7c16n,
    0x61c8864680b583ebn, 0x61c8864680b583ean, 0x80000000n, 0xffffffff80000000n];
  const out = new Uint32Array(2);
  let bad = 0, first = '';
  const check = (x) => {
    const want = sm64Big(x);
    sm64Pair(Number(x >> 32n), Number(x & 0xffffffffn), out);
    const got = (BigInt(out[0]) << 32n) | BigInt(out[1]);
    if (got !== want) { if (!bad) first = `x=0x${x.toString(16)} want 0x${want.toString(16)} got 0x${got.toString(16)}`; bad++; }
  };
  for (const x of edges) check(x);
  for (let i = 0; i < M; i++) check((BigInt(r[2 * i]) << 32n) | BigInt(r[2 * i + 1]));
  report(bad === 0, `sm64: fast (hi,lo) == BigInt reference on ${M + edges.length} inputs`, bad ? first : '');

  // Small-counter inputs as used by the engine (x = base + offset, carries across 2^32).
  bad = 0;
  for (let i = 0; i < 200_000; i++) check(BigInt(i) + (BigInt(r[i]) << 32n) + 0xffff0000n);
  report(bad === 0, 'sm64: 200000 inputs straddling 32-bit carries', bad ? first : '');

  let mbad = 0;
  const r2 = randU32s(3 * 200_000);
  for (let i = 0; i < 200_000; i++) {
    const hi = r2[3 * i], lo = r2[3 * i + 1], m = 1 + (r2[3 * i + 2] % (1 << 20));
    const want = Number(((BigInt(hi) << 32n) | BigInt(lo)) % BigInt(m));
    if (modU64(hi, lo, m) !== want) mbad++;
  }
  report(mbad === 0, 'u64 % m (m <= 2^20) == BigInt on 200000 inputs');
}

// ---------------------------------------------------------------------------
// 2. evaluate(): JS fast / JS naive vs tol.c fast / tol.c -DNAIVE (tapes and ops)
// ---------------------------------------------------------------------------
function makeTapes(count, seed) {
  // Mixture: uniform random bytes, and tapes over the BFF alphabet + 0 (dense code, many loops).
  const tapes = new Uint8Array(count * 128);
  const alpha = [...'<>{}+-.,[]'].map((c) => c.charCodeAt(0)).concat([0, 0, 1, 255]);
  let s = seed >>> 0;
  const rnd = () => { s = (s + 0x6d2b79f5) >>> 0; let t = s; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return (t ^ (t >>> 14)) >>> 0; };
  const rep = new TextEncoder().encode('[[{.>]-]');
  for (let k = 0; k < count; k++) {
    const kind = k % 4;
    for (let i = 0; i < 128; i++) {
      const x = rnd();
      tapes[k * 128 + i] = kind === 0 ? x & 255 : kind === 3 && x % 3 ? x & 255 : alpha[x % alpha.length];
    }
    if (kind === 2) { tapes.set(rep, k * 128); tapes.set([...rep].reverse(), k * 128 + 56); }
  }
  return tapes;
}
function runHarness(bin, tapes, heads, steps) {
  const out = execFileSync(bin, [heads ? '1' : '0', String(steps)], { input: tapes, maxBuffer: 1 << 30 });
  return out;
}
for (const heads of ONLY ? [] : [false, true]) {
  const COUNT = 100_000;
  const tapes = makeTapes(COUNT, heads ? 99 : 42);
  for (const steps of [8192, 1000]) {
    const cFast = runHarness(H_FAST, tapes, heads, steps);
    const cNaive = runHarness(H_NAIVE, tapes, heads, steps);
    let badF = 0, badN = 0, badC = 0, opsSum = 0;
    const t = new Uint8Array(128), t2 = new Uint8Array(128);
    for (let k = 0; k < COUNT; k++) {
      const off = k * 132;
      const cOpsF = cFast.readUInt32LE(off + 128), cOpsN = cNaive.readUInt32LE(off + 128);
      if (cOpsF !== cOpsN || Buffer.compare(cFast.subarray(off, off + 128), cNaive.subarray(off, off + 128))) badC++;
      t.set(tapes.subarray(k * 128, k * 128 + 128)); t2.set(t);
      const opsF = evaluate(t, steps, { heads });
      const opsN = evaluate(t2, steps, { heads, naive: true });
      opsSum += opsF;
      const ref = cNaive.subarray(off, off + 128);
      if (opsF !== cOpsN || Buffer.compare(Buffer.from(t.buffer), ref)) badF++;
      if (opsN !== cOpsN || Buffer.compare(Buffer.from(t2.buffer), ref)) badN++;
    }
    const tag = `${heads ? 'heads' : 'noheads'}, ${steps} steps, ${COUNT} tapes`;
    report(badF === 0 && badN === 0 && badC === 0,
      `evaluate: JS fast & JS naive == tol.c (fast & -DNAIVE), tapes and op counts [${tag}]`,
      `mismatches jsFast=${badF} jsNaive=${badN} cFast-vs-cNaive=${badC}; mean ops ${(opsSum / COUNT).toFixed(1)}`);
  }
}

// ---------------------------------------------------------------------------
// 3. Whole soups vs tol checkpoints
// ---------------------------------------------------------------------------
function tol(args) {
  const out = execFileSync(TOL, args, { encoding: 'utf8' });
  return JSON.parse(out.trim().split('\n').pop());
}
function readLog(file) {
  const rows = new Map();
  for (const line of fs.readFileSync(file, 'utf8').trim().split('\n').slice(1)) {
    const [done, h0, , , opr] = line.split(',');
    rows.set(Number(done), { h0: Number(h0), opr: Number(opr) });
  }
  return rows;
}
const finals = {};
/**
 * name, tolArgs (without --max-epochs/--checkpoint*), makeSoup(naive) -> soup,
 * maxEpochs, every. Returns the final fast soup.
 */
function soupCase({ name, tolArgs, makeSoup, maxEpochs, every, variants = QUICK ? ['fast'] : ['fast', 'naive'], needed = false }) {
  if (ONLY && !name.startsWith(ONLY) && !needed) return null;
  const dir = path.join(WORK, name), logf = path.join(WORK, `${name}.csv`);
  fs.mkdirSync(dir, { recursive: true });
  const t0 = now();
  const res = tol([...tolArgs, '--max-epochs', String(maxEpochs), '--checkpoint-dir', dir,
    '--checkpoint-every', String(every), '--threshold', '99', '--log-every', '1', '--log', logf]);
  const tolSec = (now() - t0) / 1000;
  const files = fs.readdirSync(dir).filter((f) => f.endsWith('.dat')).sort();
  const log = readLog(logf);
  let fastSoup = null;
  const opsByVariant = {};
  for (const v of variants) {
    const soup = makeSoup(v === 'naive');
    const start = soup.epoch;
    let compared = 0, same = 0, firstBad = null, opsBad = 0, h0Bad = 0;
    const ops = [];
    const t1 = now();
    while (soup.epoch < maxEpochs) {
      const e = soup.epoch;
      const o = soup.runEpoch();
      ops.push(o);
      const row = log.get(e + 1);
      if (!row || Math.abs(o / Math.floor(soup.N / 2) - row.opr) > 0.005 + 1e-9) opsBad++;
      if (e % every === 0) {
        const f = path.join(dir, `${pad10(e)}.dat`);
        const want = fs.readFileSync(f);
        const got = Buffer.from(soup.toCheckpoint());
        compared++;
        if (Buffer.compare(want, got) === 0) same++;
        else if (firstBad === null) {
          let at = 0; while (at < got.length && got[at] === want[at]) at++;
          firstBad = `${pad10(e)}.dat differs at byte ${at}`;
        }
        if (Math.abs(soup.measure() - row.h0) > 1e-5 + 1e-12) h0Bad++;
      }
    }
    const jsSec = (now() - t1) / 1000;
    opsByVariant[v] = ops;
    report(same === compared && compared === files.length,
      `${name} [JS ${v}]: ${same}/${files.length} tol checkpoints byte-identical (epochs ${start}..${maxEpochs - 1})`,
      firstBad ?? `JS ${(jsSec * 1000 / (maxEpochs - start)).toFixed(1)} ms/epoch; tol with per-epoch logging ${(tolSec * 1000 / (maxEpochs - start)).toFixed(1)} ms/epoch`);
    report(opsBad === 0 && h0Bad === 0, `${name} [JS ${v}]: ops/run and H0 match tol's log every epoch`,
      opsBad || h0Bad ? `ops mismatches ${opsBad}, h0 mismatches ${h0Bad}` : '');
    if (v === 'fast') fastSoup = soup;
  }
  if (opsByVariant.fast && opsByVariant.naive) {
    const same = opsByVariant.fast.every((x, i) => x === opsByVariant.naive[i]);
    report(same, `${name}: JS fast and naive op counts identical every epoch`);
  }
  finals[name] = { soup: fastSoup, res, dir };
  return fastSoup;
}

// (a) noheads, default mutation
soupCase({
  name: 'a_noheads', tolArgs: ['--num', '4096', '--seed', '7'],
  makeSoup: (naive) => createSoup({ N: 4096, seed: 7, naive }), maxEpochs: 601, every: 100,
  needed: !!ONLY && 'd_replay'.startsWith(ONLY), // (d) starts from one of its checkpoints
});
// (b) heads
soupCase({
  name: 'b_heads', tolArgs: ['--num', '4096', '--seed', '8', '--heads'],
  makeSoup: (naive) => createSoup({ N: 4096, seed: 8, heads: true, naive }), maxEpochs: 601, every: 100,
});
// (c) no mutation
soupCase({
  name: 'c_nomut', tolArgs: ['--num', '4096', '--seed', '9', '--mut', '0'],
  makeSoup: (naive) => createSoup({ N: 4096, seed: 9, mutProb: 0, naive }), maxEpochs: 601, every: 100,
});
// (d) replay: load (a)'s checkpoint after epoch index 300 (epochs_done 301) with a different seed
if (finals.a_noheads) {
  const ck = path.join(finals.a_noheads.dir, `${pad10(300)}.dat`);
  const S2 = '18446744073709551557'; // > 2^63: exercises full u64 seeds
  const soup = soupCase({
    name: 'd_replay', tolArgs: ['--load', ck, '--seed', S2],
    makeSoup: (naive) => {
      const s = loadCheckpoint(fs.readFileSync(ck), { seed: 7, naive });
      if (s.epoch !== 301) throw new Error(`loaded epoch ${s.epoch}, expected 301`);
      return s.setSeed(S2);
    },
    maxEpochs: 601, every: 100,
  });
  if (soup) {
    const a = finals.a_noheads.soup.bytes;
    let diff = 0; for (let i = 0; i < a.length; i++) diff += a[i] !== soup.bytes[i];
    report(diff > 0, 'd_replay: replay with the new seed diverges from the original run (sanity)', `${diff} bytes differ at epoch 601`);
  }
}
// (e) replicator-rich soup: every 16th program is the palindromic replicator
const REP = (() => {
  const r = new Uint8Array(64);
  r.set(new TextEncoder().encode('[[{.>]-]'), 0);
  r.set(new TextEncoder().encode(']-]>.{[['), 56);
  return r;
})();
function seededCheckpoint(N, seed) {
  const buf = new ArrayBuffer(24 + N * 64), dv = new DataView(buf), u8 = new Uint8Array(buf, 24);
  dv.setBigUint64(0, 0n, true); dv.setBigUint64(8, BigInt(N), true); dv.setBigUint64(16, 0n, true);
  let s = seed >>> 0;
  for (let p = 0; p < N; p++) {
    if (p % 16 === 0) { u8.set(REP, p * 64); continue; }
    for (let i = 0; i < 64; i++) { s ^= s << 13; s ^= s >>> 17; s ^= s << 5; u8[p * 64 + i] = s & 255; }
  }
  return Buffer.from(buf);
}
// Census: number of distinct programs and the count of the most common one.
function census(bytes) {
  const m = new Map();
  for (let p = 0; p < bytes.length; p += 64) {
    const k = Buffer.from(bytes.subarray(p, p + 64)).toString('latin1');
    m.set(k, (m.get(k) || 0) + 1);
  }
  return { distinct: m.size, top: Math.max(...m.values()) };
}
{
  const ckE = path.join(WORK, 'seeded.dat');
  fs.writeFileSync(ckE, seededCheckpoint(8192, 5));
  const s0 = loadCheckpoint(fs.readFileSync(ckE));
  const h0Start = s0.measure(), c0 = census(s0.bytes);
  const soup = soupCase({
    name: 'e_replicators', tolArgs: ['--load', ckE, '--seed', '6'],
    makeSoup: (naive) => loadCheckpoint(fs.readFileSync(ckE), { seed: 6, naive }), maxEpochs: 601, every: 50,
  });
  // (The replicator's '-]' turns its 48 zero bytes into 0xFF on the first copy; that form
  // spreads to ~1800 copies by epoch 25 and then diversifies.)
  if (soup) {
    const c1 = census(soup.bytes);
    console.log(`      e_replicators: epoch 0 -> 601: H0 ${h0Start.toFixed(2)} -> ${soup.measure().toFixed(2)} bits/byte, ` +
      `distinct programs ${c0.distinct} -> ${c1.distinct} of 8192, most common program x${c0.top} -> x${c1.top}`);
  }
}
// (f) odd N, maximal u64 seed, non-dyadic mutation rate
soupCase({
  name: 'f_oddN', tolArgs: ['--num', '1001', '--seed', '18446744073709551615', '--mut', '0.01'],
  makeSoup: (naive) => createSoup({ N: 1001, seed: 18446744073709551615n, mutProb: 0.01, naive }),
  maxEpochs: 401, every: 50,
});
// (g) heads + replicator-rich (loops and copies under the other variant)
{
  const ckG = path.join(WORK, 'seeded_g.dat');
  fs.writeFileSync(ckG, seededCheckpoint(4096, 11));
  soupCase({
    name: 'g_heads_seeded', tolArgs: ['--load', ckG, '--seed', '12', '--heads'],
    makeSoup: (naive) => loadCheckpoint(fs.readFileSync(ckG), { seed: 12, heads: true, naive }),
    maxEpochs: 401, every: 50,
  });
}

// (i) 32-bit carries inside the per-epoch counters. Each u64 stream is base + small
// offset; offset + low word of base crosses 2^32 only with probability ~64N/2^32 per
// epoch, so ordinary runs almost never exercise it. Find seeds/epochs where it happens.
// Note: for power-of-two N, lo(base) mod (stride*N) is fixed by GOLDEN's low bits, so a
// given stream can carry for some N and never for others (e.g. the mutation stream can
// never carry for N = 4096, 16384 or 131072, but can for N = 8192).
{
  const W = 1n << 32n, G = 0x9e3779b97f4a7c15n, GL = G & 0xffffffffn;
  const lo = (x) => BigInt.asUintN(64, x) & 0xffffffffn;
  const search = (what, pred, limit = 2_000_000) => {
    for (let x = 0; x < limit; x++) if (pred(BigInt(x))) return x;
    throw new Error(`no ${what} carry found`);
  };
  // init: sm64(64*N*s0 + j), j < 64N
  const nI = 4096n;
  const sInit = search('init', (s) => lo(64n * nI * seedfBig(s, 0n) + G) > W - 64n * nI);
  // shuffle: sm64(E*N + i), 1 <= i < N -> E with lo(E*N + G) in (W - N, W); solvable directly
  const nS = 4096n;
  const eShuf = Number(((W - nS + (GL % nS) - GL + W) % W) / nS);
  if (!(lo(BigInt(eShuf) * nS + G) > W - nS)) throw new Error('no shuffle carry found');
  // mutation: sm64(128*N*seedf(E) + 128k + i), 128k + i < 64N
  const nM = 8192n, sMut = 21n;
  const eMut = search('mutation', (e) => lo(128n * nM * seedfBig(sMut, e) + G) > W - 64n * nM);
  soupCase({
    name: 'i_carry_init', tolArgs: ['--num', String(nI), '--seed', String(sInit)],
    makeSoup: (naive) => createSoup({ N: Number(nI), seed: sInit, naive }), maxEpochs: 2, every: 1,
  });
  for (const [name, N, E, seed] of [['i_carry_shuffle', Number(nS), eShuf, 5n], ['i_carry_mutation', Number(nM), eMut, sMut]]) {
    const ck = path.join(WORK, `${name}.dat`);
    const buf = Buffer.from(createSoup({ N, seed: 99 }).toCheckpoint());
    buf.writeBigUInt64LE(BigInt(E), 16); // a random soup whose header says E epochs are done
    fs.writeFileSync(ck, buf);
    soupCase({
      name, tolArgs: ['--load', ck, '--seed', String(seed)],
      makeSoup: (naive) => loadCheckpoint(fs.readFileSync(ck), { seed, naive }), maxEpochs: E + 2, every: 1,
    });
  }
  if (!ONLY || 'i_carry'.startsWith(ONLY) || ONLY.startsWith('i_carry'))
    console.log(`      carry cases: init N=4096 seed ${sInit}; shuffle N=4096 epoch ${eShuf}; mutation N=8192 seed ${sMut} epoch ${eMut}`);
}

// ---------------------------------------------------------------------------
// 4. Speed (N = 16384, noheads, default mutation) + exactness at that size
// ---------------------------------------------------------------------------
if (BENCH) {
  console.log('\nspeed, node ' + process.version + ', N=16384 bff_noheads p=1/4096:');
  const E = 300;
  const soup = soupCase({
    name: 'h_bench_N16384', tolArgs: ['--num', '16384', '--seed', '1'],
    makeSoup: (naive) => createSoup({ N: 16384, seed: 1, naive }), maxEpochs: E + 1, every: 100,
    variants: ['fast'],
  });
  const timeRun = (s, n) => { const t = now(); for (let i = 0; i < n; i++) s.runEpoch(); return (now() - t) / n; };
  const t0 = now(); createSoup({ N: 16384, seed: 1 }); const tInit = now() - t0;
  const base = createSoup({ N: 16384, seed: 1 });
  const msDefault = timeRun(base, 200);
  const noMut = createSoup({ N: 16384, seed: 1, mutProb: 0 });
  const msNoMut = timeRun(noMut, 200);
  const nv = createSoup({ N: 16384, seed: 1, naive: true });
  const msNaive = timeRun(nv, 50);
  const tc0 = now();
  tol(['--num', '16384', '--seed', '1', '--max-epochs', '200', '--threshold', '99', '--log-every', '1000000']);
  const cMs = (now() - tc0) / 200;
  console.log(`      createSoup: ${tInit.toFixed(1)} ms`);
  console.log(`      runEpoch (fast interpreter, epochs 0-199): ${msDefault.toFixed(2)} ms/epoch   [tol -O3 same run: ${cMs.toFixed(2)} ms/epoch incl. process start]`);
  console.log(`      runEpoch with mutProb=0 (no mutation RNG): ${msNoMut.toFixed(2)} ms/epoch  => mutation RNG ~${(msDefault - msNoMut).toFixed(2)} ms/epoch`);
  console.log(`      runEpoch (naive interpreter, epochs 0-49): ${msNaive.toFixed(2)} ms/epoch`);
  // Alive regime: replicator-seeded soup after takeover.
  const ckB = path.join(WORK, 'seeded_bench.dat');
  fs.writeFileSync(ckB, seededCheckpoint(16384, 3));
  const alive = loadCheckpoint(fs.readFileSync(ckB), { seed: 3 });
  for (let i = 0; i < 100; i++) alive.runEpoch();
  const msAlive = timeRun(alive, 100);
  const tc = now();
  tol(['--load', ckB, '--seed', '3', '--max-epochs', '200', '--threshold', '99', '--log-every', '1000000']);
  const cAlive = (now() - tc) / 200;
  console.log(`      replicator-seeded N=16384 (epochs 100-199): JS ${msAlive.toFixed(2)} ms/epoch; tol -O3 ${cAlive.toFixed(2)} ms/epoch (epochs 0-199, incl. process start)`);
}

console.log(`\n${failures === 0 ? 'ALL PASS' : failures + ' FAILURE(S)'}`);
if (!KEEP) fs.rmSync(WORK, { recursive: true, force: true });
else console.log(`kept ${WORK}`);
process.exit(failures === 0 ? 0 : 1);
