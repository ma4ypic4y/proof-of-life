// tol.c — "Tape of Life" soup engine.
//
// A single-threaded, byte-exact re-implementation of the BFF primordial soup
// from Agüera y Arcas et al., "Computational Life" (arXiv:2406.19108), following
// the reference code github.com/paradigms-of-intelligence/cubff:
//   * same interpreter semantics (bff_noheads = the paper's BFF; --heads = cubff "bff")
//   * same SplitMix64 streams for initialisation, pairing shuffle and mutation
//   * same checkpoint file format (3 x u64 header + soup bytes)
// Given the same seed, the soup after every epoch is identical to cubff's.
//
// What this adds on top of cubff:
//   * a RAM ring buffer of past soups, dumped when the soup "comes alive",
//     so that a world can be rewound to before its origin of life and replayed
//     under different random collisions (the fork/replay experiments);
//   * a census of the most abundant programs at the end of a run.
//
// Build: cc -O3 -march=native tol.c -lbrotlienc -lm -o tol

#include <brotli/encode.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define T1 64
#define T2 128
#define STEP_LIMIT 8192

static inline uint64_t sm64(uint64_t s) {
  uint64_t z = s + 0x9e3779b97f4a7c15ULL;
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}

static uint64_t g_pseed;  // params.seed in cubff
static inline uint64_t seedf(uint64_t x) { return sm64(sm64(g_pseed) ^ sm64(x)); }

// ---------------------------------------------------------------------------
// Interpreter. Mirrors Bff::Evaluate / Bff::EvaluateOne in cubff/bff.inc.h.
// Returns the number of non-noop instructions executed.
// ---------------------------------------------------------------------------
static int g_heads = 0;  // 0: bff_noheads (paper), 1: heads read from tape[0], tape[1]
#ifdef COUNT_STEPS
static uint64_t g_sim = 0;  // interpreter iterations actually simulated
#endif

static const uint8_t OPC[256] = {['<'] = 1, ['>'] = 1, ['{'] = 1, ['}'] = 1, ['+'] = 1,
                                 ['-'] = 1, ['.'] = 1, [','] = 1, ['['] = 1, [']'] = 1};

// Two exact shortcuts (disabled with -DNAIVE, which the validation uses):
//
// 1. Runs of no-op bytes. 246 of 256 byte values do nothing, so a random tape
//    is mostly filler. A run of k no-ops costs k steps and changes nothing
//    else, so we consume it in one go (respecting the step budget).
//
// 2. Cycles. The future of an execution depends only on (pos, h0, h1, tape).
//    We watch the states right after backward jumps with Brent's cycle
//    detection (reference state re-anchored after 1, 2, 4, 8... jumps, full
//    128-byte comparison on a match of pos and heads). Once a state recurs the
//    run is periodic with period c and can never terminate, so the tape at the
//    step limit is the tape (stepcount - 1 - i) mod c iterations from now: we
//    skip whole periods and simulate the remainder.
static uint32_t evaluate(uint8_t *t, uint32_t stepcount) {
  int pos = 0, h0 = 0, h1 = 0;
  if (g_heads) {
    h0 = t[0] % T2;
    h1 = t[1] % T2;
    pos = 2;
  }
  uint32_t i = 0, nskip = 0;
#ifndef NAIVE
  int skipped = 0, have_ref = 0, ref_pos = 0, ref_h0 = 0, ref_h1 = 0;
  uint32_t ref_i = 0, ref_nskip = 0, power = 1, lam = 0;
  uint8_t ref_tape[T2];
  // Write-free anchor: the first backward jump after the last tape change.
  // Catches drifting loops (heads wrap after <=128 laps) without waiting for
  // Brent's power-of-two schedule.
  int a_pos = -1, a_h0 = 0, a_h1 = 0;
  uint32_t a_i = 0, a_nskip = 0;
#define CHANGED() (a_pos = -1)
#else
#define CHANGED() ((void)0)
#endif
  for (; i < stepcount; i++) {
#ifdef COUNT_STEPS
    g_sim++;
#endif
    h0 &= T2 - 1;
    h1 &= T2 - 1;
    switch (t[pos]) {
      case '<': h0--; break;
      case '>': h0++; break;
      case '{': h1--; break;
      case '}': h1++; break;
      case '+': t[h0]++; CHANGED(); break;
      case '-': t[h0]--; CHANGED(); break;
      case '.': if (t[h1] != t[h0]) { t[h1] = t[h0]; CHANGED(); } break;
      case ',': if (t[h0] != t[h1]) { t[h0] = t[h1]; CHANGED(); } break;
      case '[':
        if (t[h0] == 0) {
          int d = 1;
          pos++;
          for (; pos < T2 && d > 0; pos++) {
            if (t[pos] == ']') d--;
            if (t[pos] == '[') d++;
          }
          pos--;
          if (d != 0) pos = T2;
        }
        break;
      case ']':
        if (t[h0] != 0) {
          int d = 1;
          pos--;
          for (; pos >= 0 && d > 0; pos--) {
            if (t[pos] == ']') d++;
            if (t[pos] == '[') d--;
          }
          pos++;
          if (d != 0) pos = -1;
#ifndef NAIVE
          else if (!skipped) {
            uint32_t c = 0, c_nskip = 0;
            if (a_pos == pos && a_h0 == h0 && a_h1 == h1) {
              c = i - a_i; c_nskip = nskip - a_nskip;
            } else if (have_ref && pos == ref_pos && h0 == ref_h0 && h1 == ref_h1 &&
                       !memcmp(t, ref_tape, T2)) {
              c = i - ref_i; c_nskip = nskip - ref_nskip;
            }
            if (c) {
              uint32_t rem = (stepcount - 1 - i) % c;
              uint32_t cycles = (stepcount - 1 - i - rem) / c;
              nskip += cycles * c_nskip;
              i = stepcount - rem - 1;
              skipped = 1;
              break;
            }
            if (a_pos < 0 || i - a_i > 3000) {
              a_pos = pos; a_h0 = h0; a_h1 = h1; a_i = i; a_nskip = nskip;
            }
            if (!have_ref || ++lam >= power) {
              if (have_ref) power <<= 1;
              lam = 0;
              have_ref = 1;
              ref_pos = pos; ref_h0 = h0; ref_h1 = h1; ref_i = i; ref_nskip = nskip;
              memcpy(ref_tape, t, T2);
            }
          }
#endif
        }
        break;
      default: {
#ifndef NAIVE
        uint32_t room = stepcount - i;
        int end = pos + (room < (uint32_t)(T2 - pos) ? (int)room : T2 - pos);
        int p = pos + 1;
        while (p < end && !OPC[t[p]]) p++;
        nskip += p - pos;
        i += p - pos - 1;
        pos = p - 1;
#else
        nskip++;
#endif
      }
    }
    if (pos < 0) { i++; break; }
    pos++;
    if (pos >= T2) { i++; break; }
  }
  return i - nskip;
}

// ---------------------------------------------------------------------------
// Replication score. Mirrors CheckSelfRep in cubff/common_language.h:
// pair the program with 13 noise partners, run 1 + 4 generations (each time the
// copy that landed in the right half becomes the new left half), and count how
// many positions of both halves are reproduced consistently. A score >= 5 is
// cubff's threshold for "this looks like a self-replicator".
// ---------------------------------------------------------------------------
static int selfrep_score(const uint8_t *prog, uint64_t local_seed) {
  enum { ITERS = 13, GENS = 4 };
  uint8_t tapes[ITERS][T2];
  for (int i = 0; i < ITERS; i++) {
    uint8_t noise[T1];
    for (int j = 0; j < T1; j++)
      noise[j] = sm64(local_seed ^ sm64((uint64_t)(i + 1) * T1 + j)) % 256;
    uint8_t *tape = tapes[i];
    memcpy(tape, prog, T1);
    memcpy(tape + T1, noise, T1);
    evaluate(tape, STEP_LIMIT);
    for (int g = 0; g < GENS; g++) {
      memcpy(tape, tape + T1, T1);
      memcpy(tape + T1, noise, T1);
      evaluate(tape, STEP_LIMIT);
    }
  }
  int res[2] = {0, 0};
  for (int i = 0; i < T2; i++) {
    for (int a = 0; a < ITERS; a++) {
      int count = 1;
      if (i < T1 && tapes[a][i] != prog[i]) continue;
      for (int b = a + 1; b < ITERS; b++)
        if (tapes[a][i] == tapes[b][i]) count++;
      if (count > ITERS / 4) { res[i / T1]++; break; }
    }
  }
  return res[0] < res[1] ? res[0] : res[1];
}

// ---------------------------------------------------------------------------
// Soup
// ---------------------------------------------------------------------------
static size_t N;
static uint8_t *soup;
static uint32_t *perm;
static uint32_t mut_prob;  // out of 2^30

static void init_soup(void) {
  uint64_t s0 = seedf(0);
  for (size_t idx = 0; idx < N; idx++)
    for (size_t i = 0; i < T1; i++)
      soup[idx * T1 + i] = sm64(T1 * N * s0 + T1 * idx + i) % 256;
}

static uint64_t run_epoch(uint64_t epoch) {
  for (size_t i = 0; i < N; i++) perm[i] = i;
  for (size_t i = N; i-- > 0;) {
    size_t j = sm64(seedf(epoch * N + i)) % (i + 1);
    uint32_t tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
  }
  uint64_t es = seedf(epoch);
  uint64_t ops = 0;
  uint8_t tape[T2];
  for (size_t k = 0; k < N / 2; k++) {
    uint8_t *a = soup + (size_t)perm[2 * k] * T1;
    uint8_t *b = soup + (size_t)perm[2 * k + 1] * T1;
    memcpy(tape, a, T1);
    memcpy(tape + T1, b, T1);
    if (mut_prob) {
      for (size_t i = 0; i < T2; i++) {
        uint64_t rng = sm64((N * es + k) * T2 + i);
        if (((rng >> 8) & ((1ULL << 30) - 1)) < mut_prob) tape[i] = rng & 0xFF;
      }
    }
    ops += evaluate(tape, STEP_LIMIT);
    memcpy(a, tape, T1);
    memcpy(b, tape + T1, T1);
  }
  return ops;
}

static uint8_t *brotli_buf;
static size_t brotli_cap;
static void measure(double *h0_out, double *he_out, size_t *bsize_out) {
  size_t total = N * T1;
  uint64_t counts[256] = {0};
  for (size_t i = 0; i < total; i++) counts[soup[i]]++;
  double h0 = 0;
  for (int i = 0; i < 256; i++)
    if (counts[i]) { double f = (double)counts[i] / total; h0 -= f * log2(f); }
  size_t bs = brotli_cap;
  BrotliEncoderCompress(2, 24, BROTLI_MODE_GENERIC, total, soup, &bs, brotli_buf);
  *h0_out = h0;
  *he_out = h0 - bs * 8.0 / total;
  *bsize_out = bs;
}

static void save_soup(const char *path, uint64_t epochs_done) {
  FILE *f = fopen(path, "wb");
  if (!f) { perror(path); exit(1); }
  uint64_t hdr[3] = {1, N, epochs_done};
  fwrite(hdr, 8, 3, f);
  fwrite(soup, 1, N * T1, f);
  fclose(f);
}

static uint64_t load_soup(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) { perror(path); exit(1); }
  uint64_t hdr[3];
  if (fread(hdr, 8, 3, f) != 3) { fprintf(stderr, "bad header\n"); exit(1); }
  N = hdr[1];
  soup = malloc(N * T1);
  if (fread(soup, 1, N * T1, f) != N * T1) { fprintf(stderr, "short soup\n"); exit(1); }
  fclose(f);
  return hdr[2];
}

// Most abundant exact programs (open-addressing hash of 64-byte strings).
typedef struct { uint32_t idx; uint32_t count; } Slot;
static uint64_t hash64(const uint8_t *p) {
  uint64_t h = 0x12345;
  for (int i = 0; i < T1; i += 8) { uint64_t w; memcpy(&w, p + i, 8); h = sm64(h ^ w); }
  return h;
}
static void census(FILE *out, int topk, uint64_t epochs_done) {
  size_t cap = 1; while (cap < 2 * N) cap <<= 1;
  Slot *tab = calloc(cap, sizeof(Slot));
  for (size_t i = 0; i < N; i++) {
    const uint8_t *p = soup + i * T1;
    size_t h = hash64(p) & (cap - 1);
    while (tab[h].count && memcmp(soup + (size_t)tab[h].idx * T1, p, T1)) h = (h + 1) & (cap - 1);
    if (!tab[h].count) tab[h].idx = i;
    tab[h].count++;
  }
  size_t distinct = 0;
  for (size_t i = 0; i < cap; i++) distinct += tab[i].count > 0;
  fprintf(out, "{\"epoch\":%llu,\"distinct\":%zu,\"top\":[", (unsigned long long)epochs_done, distinct);
  for (int r = 0; r < topk; r++) {
    size_t best = cap;
    for (size_t i = 0; i < cap; i++)
      if (tab[i].count && (best == cap || tab[i].count > tab[best].count)) best = i;
    if (best == cap) break;
    const uint8_t *p = soup + (size_t)tab[best].idx * T1;
    int score = selfrep_score(p, sm64(g_pseed ^ 0xC0FFEE));
    fprintf(out, "%s{\"count\":%u,\"selfrep\":%d,\"hex\":\"", r ? "," : "", tab[best].count, score);
    for (int i = 0; i < T1; i++) fprintf(out, "%02x", p[i]);
    fprintf(out, "\"}");
    tab[best].count = 0;
  }
  fprintf(out, "]}\n");
  free(tab);
}

static double now_s(void) {
  struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static void usage(void) {
  fprintf(stderr,
    "tol: BFF primordial soup (cubff-exact)\n"
    "  --seed S          params.seed (default 0)\n"
    "  --num N           programs (default 131072)\n"
    "  --mut P           mutation probability (default 1/4096, as cubff)\n"
    "  --heads           cubff 'bff' variant (heads from tape[0],tape[1]); default bff_noheads\n"
    "  --load F          start from a checkpoint (cubff format)\n"
    "  --max-epochs E    stop after E total epochs (default 16384)\n"
    "  --log-every L     measure complexity every L epochs (default 16)\n"
    "  --log F           CSV log of epoch,h0,higher_entropy,brotli,ops_per_run\n"
    "  --threshold X     higher-order entropy marking a transition (default 3.0)\n"
    "  --tail K          keep running K epochs after the transition (default 256)\n"
    "  --ring-every R    keep a RAM snapshot every R epochs (default 0 = off)\n"
    "  --ring-size M     number of ring snapshots kept (default 64)\n"
    "  --dump-dir D      on transition, dump ring snapshots to D/<epochs_done>.dat\n"
    "  --census F        append a JSON census (top programs) at the end to F\n"
    "  --checkpoint-dir D --checkpoint-every C   cubff-style saves (for validation)\n"
    "  --result F        append one JSON result line to F\n"
    "  --save-final F    if the soup came alive, save the final soup to F\n"
    "  --track HEX       per-epoch census of one lineage: programs identical to HEX\n"
    "                    and programs sharing >= 32 of 64 bytes with it (or with its reverse)\n"
    "  --track-log F --track-from E   where to log it, and from which epoch on\n"
    "  --save-at E1,E2,.. --save-prefix P   save the soup to P<E>.dat once E epochs are done\n");
  exit(1);
}

int main(int argc, char **argv) {
  uint64_t seed = 0, max_epochs = 16384, log_every = 16, tail = 256;
  uint64_t ring_every = 0, ring_size = 64, ckpt_every = 0;
  double mutp = 1.0 / 4096, threshold = 3.0;
  const char *load = NULL, *logf = NULL, *dump_dir = NULL, *census_f = NULL,
             *ckpt_dir = NULL, *result_f = NULL, *save_final = NULL, *track_hex = NULL,
             *track_log = NULL;
  uint64_t track_from = 0;
  const char *save_at = NULL, *save_prefix = "snap_";
  N = 131072;
  for (int i = 1; i < argc; i++) {
    const char *a = argv[i];
#define ARG (i + 1 < argc ? argv[++i] : (usage(), ""))
    if (!strcmp(a, "--seed")) seed = strtoull(ARG, 0, 10);
    else if (!strcmp(a, "--num")) N = strtoull(ARG, 0, 10);
    else if (!strcmp(a, "--mut")) mutp = atof(ARG);
    else if (!strcmp(a, "--heads")) g_heads = 1;
    else if (!strcmp(a, "--load")) load = ARG;
    else if (!strcmp(a, "--max-epochs")) max_epochs = strtoull(ARG, 0, 10);
    else if (!strcmp(a, "--log-every")) log_every = strtoull(ARG, 0, 10);
    else if (!strcmp(a, "--log")) logf = ARG;
    else if (!strcmp(a, "--threshold")) threshold = atof(ARG);
    else if (!strcmp(a, "--tail")) tail = strtoull(ARG, 0, 10);
    else if (!strcmp(a, "--ring-every")) ring_every = strtoull(ARG, 0, 10);
    else if (!strcmp(a, "--ring-size")) ring_size = strtoull(ARG, 0, 10);
    else if (!strcmp(a, "--dump-dir")) dump_dir = ARG;
    else if (!strcmp(a, "--census")) census_f = ARG;
    else if (!strcmp(a, "--checkpoint-dir")) ckpt_dir = ARG;
    else if (!strcmp(a, "--checkpoint-every")) ckpt_every = strtoull(ARG, 0, 10);
    else if (!strcmp(a, "--result")) result_f = ARG;
    else if (!strcmp(a, "--save-final")) save_final = ARG;
    else if (!strcmp(a, "--track")) track_hex = ARG;
    else if (!strcmp(a, "--track-log")) track_log = ARG;
    else if (!strcmp(a, "--track-from")) track_from = strtoull(ARG, 0, 10);
    else if (!strcmp(a, "--save-at")) save_at = ARG;
    else if (!strcmp(a, "--save-prefix")) save_prefix = ARG;
    else usage();
  }
  g_pseed = seed;
  mut_prob = (uint32_t)llround(mutp * (1 << 30));

  uint64_t epoch = 0;
  if (load) epoch = load_soup(load);
  else { soup = malloc(N * T1); init_soup(); }
  perm = malloc(N * sizeof(uint32_t));
  brotli_cap = BrotliEncoderMaxCompressedSize(N * T1);
  brotli_buf = malloc(brotli_cap);

  uint8_t *ring = NULL; uint64_t *ring_epoch = NULL;
  if (ring_every) {
    ring = malloc(ring_size * N * T1);
    ring_epoch = calloc(ring_size, sizeof(uint64_t));
    for (uint64_t r = 0; r < ring_size; r++) ring_epoch[r] = UINT64_MAX;
  }
  FILE *lf = logf ? fopen(logf, "w") : NULL;
  if (lf) fprintf(lf, "epoch,h0,higher_entropy,brotli_size,ops_per_run\n");

  uint8_t trk[T1], trk_rev[T1];
  FILE *tf = NULL;
  if (track_hex) {
    if (strlen(track_hex) != 2 * T1) { fprintf(stderr, "--track needs 128 hex chars\n"); exit(1); }
    for (int i = 0; i < T1; i++) { unsigned v; sscanf(track_hex + 2 * i, "%2x", &v); trk[i] = v; }
    for (int i = 0; i < T1; i++) trk_rev[i] = trk[T1 - 1 - i];
    tf = fopen(track_log ? track_log : "/dev/stdout", "w");
    fprintf(tf, "epoch,exact,near\n");
  }
  const uint64_t start_epoch = epoch;
  int64_t transition = -1;  // epochs_done at first log point above threshold
  double t0 = now_s(), ops_acc = 0; uint64_t runs_acc = 0;
  double h0 = 0, he = 0; size_t bs = 0;
  for (; epoch < max_epochs; epoch++) {
    // Ring snapshots hold the soup *before* running `epoch` (epochs_done == epoch).
    if (ring_every && epoch % ring_every == 0) {
      uint64_t r = (epoch / ring_every) % ring_size;
      memcpy(ring + r * N * T1, soup, N * T1);
      ring_epoch[r] = epoch;
    }
    ops_acc += run_epoch(epoch);
    runs_acc += N / 2;
    uint64_t done = epoch + 1;
    if (save_at) {
      for (const char *q = save_at; *q;) {
        char *e;
        if (strtoull(q, &e, 10) == done) {
          char p[4096]; snprintf(p, sizeof p, "%s%llu.dat", save_prefix, (unsigned long long)done);
          save_soup(p, done);
        }
        q = *e ? e + 1 : e;
      }
    }
    if (tf && done >= track_from) {
      uint64_t exact = 0, near = 0;
      for (size_t p = 0; p < N; p++) {
        const uint8_t *q = soup + p * T1;
        int f = 0, r = 0;
        for (int i = 0; i < T1; i++) { f += q[i] == trk[i]; r += q[i] == trk_rev[i]; }
        exact += f == T1;
        near += f >= T1 / 2 || r >= T1 / 2;
      }
      fprintf(tf, "%llu,%llu,%llu\n", (unsigned long long)done, (unsigned long long)exact, (unsigned long long)near);
    }
    if (ckpt_dir && ckpt_every && epoch % ckpt_every == 0) {
      char p[4096]; snprintf(p, sizeof p, "%s/%010llu.dat", ckpt_dir, (unsigned long long)epoch);
      save_soup(p, done);
    }
    if (epoch % log_every == 0) {
      measure(&h0, &he, &bs);
      if (lf) { fprintf(lf, "%llu,%.5f,%.5f,%zu,%.2f\n", (unsigned long long)done, h0, he, bs, ops_acc / runs_acc); fflush(lf); }
      ops_acc = 0; runs_acc = 0;
      if (transition < 0 && he > threshold) {
        transition = done;
        if (ring && dump_dir) {
          for (uint64_t r = 0; r < ring_size; r++) {
            if (ring_epoch[r] == UINT64_MAX) continue;
            // Keep every snapshot in the last 512 epochs, then thin out
            // geometrically: every 128 up to 1024 back, every 512 beyond.
            uint64_t age = done - ring_epoch[r];
            if (!(age <= 512 || (age <= 1024 && ring_epoch[r] % 128 == 0) ||
                  ring_epoch[r] % 512 == 0))
              continue;
            char p[4096]; snprintf(p, sizeof p, "%s/%010llu.dat", dump_dir, (unsigned long long)ring_epoch[r]);
            FILE *f = fopen(p, "wb");
            if (!f) { perror(p); exit(1); }
            uint64_t hdr[3] = {1, N, ring_epoch[r]};
            fwrite(hdr, 8, 3, f); fwrite(ring + r * N * T1, 1, N * T1, f); fclose(f);
          }
        }
        if (max_epochs > done + tail) max_epochs = done + tail;
      }
    }
  }
  measure(&h0, &he, &bs);
  double el = now_s() - t0;
  if (census_f) { FILE *cf = fopen(census_f, "a"); census(cf, 16, epoch); fclose(cf); }
  if (save_final && transition >= 0) save_soup(save_final, epoch);
  if (tf) fclose(tf);
  char line[1024];
  snprintf(line, sizeof line,
           "{\"seed\":%llu,\"num\":%zu,\"mut\":%g,\"heads\":%d,\"load\":\"%s\",\"start\":%llu,"
           "\"end\":%llu,\"transition\":%lld,\"final_he\":%.4f,\"seconds\":%.1f}\n",
           (unsigned long long)seed, N, mutp, g_heads, load ? load : "", (unsigned long long)start_epoch,
           (unsigned long long)epoch, (long long)transition, he, el);
  fputs(line, stdout);
  if (result_f) { FILE *rf = fopen(result_f, "a"); fputs(line, rf); fclose(rf); }
  if (lf) fclose(lf);
  return 0;
}
