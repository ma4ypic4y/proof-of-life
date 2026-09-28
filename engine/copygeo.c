// copygeo.c — how do bytes actually move between partners in a soup?
//
// Samples K random pairs (A, B) from a soup checkpoint, runs each glued tape
// with a tracing copy of the interpreter, and classifies every copy event that
// moves a byte from one half of the tape to the other:
//   mirror : dst == 127 - src          (the child is the parent reversed)
//   shift  : |dst - src| == 64         (the child is the parent, same order)
//   other  : anything else
// It also classifies each such event by direction relative to the previous
// cross-half copy by the same instruction kind in the same run: reversed (the
// read and write heads stepped in opposite directions) or forward (same
// direction). This catches mirror/forward copies with an offset. As a self-check, every traced run must leave exactly the same
// tape as tol.c's evaluate().
//
// usage: copygeo soup.dat [--pairs K] [--heads] [--seed S]
// prints one JSON line.
#define main tol_main
#include "tol.c"
#undef main

typedef struct { uint64_t mirror, shift, other, rev, fwd, runs_with_copy; } Geo;

static void traced(uint8_t *t, Geo *g) {
  int pos = 0, h0 = 0, h1 = 0;
  if (g_heads) { h0 = t[0] % T2; h1 = t[1] % T2; pos = 2; }
  int last_src = -1, last_dst = -1, last_op = 0, any = 0;
  for (uint32_t i = 0; i < STEP_LIMIT; i++) {
    h0 &= T2 - 1; h1 &= T2 - 1;
    int src = -1, dst = -1, op = t[pos];
    switch (t[pos]) {
      case '<': h0--; break;
      case '>': h0++; break;
      case '{': h1--; break;
      case '}': h1++; break;
      case '+': t[h0]++; break;
      case '-': t[h0]--; break;
      case '.': src = h0; dst = h1; t[h1] = t[h0]; break;
      case ',': src = h1; dst = h0; t[h0] = t[h1]; break;
      case '[':
        if (t[h0] == 0) {
          int d = 1; pos++;
          for (; pos < T2 && d > 0; pos++) { if (t[pos] == ']') d--; if (t[pos] == '[') d++; }
          pos--; if (d != 0) pos = T2;
        }
        break;
      case ']':
        if (t[h0] != 0) {
          int d = 1; pos--;
          for (; pos >= 0 && d > 0; pos--) { if (t[pos] == ']') d++; if (t[pos] == '[') d--; }
          pos++; if (d != 0) pos = -1;
        }
        break;
    }
    if (src >= 0 && (src < T1) != (dst < T1)) {
      any = 1;
      if (dst == T2 - 1 - src) g->mirror++;
      else if (dst - src == T1 || src - dst == T1) g->shift++;
      else g->other++;
      // Direction is only defined between two copies by the same instruction
      // kind ('.' then '.', or ',' then ','), with both heads having taken a
      // small step (wrap-aware). A '.' followed by ',' swaps source and
      // destination without any head moving, and must not count.
      if (last_src >= 0 && op == last_op) {
        int ds = ((src - last_src + 192) % 128) - 64, dd = ((dst - last_dst + 192) % 128) - 64;
        if (ds != 0 && dd != 0 && ds >= -8 && ds <= 8 && dd >= -8 && dd <= 8) {
          if ((ds > 0) != (dd > 0)) g->rev++; else g->fwd++;
        }
      }
      last_src = src; last_dst = dst; last_op = op;
    }
    if (pos < 0) break;
    pos++;
    if (pos >= T2) break;
  }
  g->runs_with_copy += any;
}

int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: copygeo soup.dat [--pairs K] [--heads] [--seed S]\n"); return 1; }
  uint64_t K = 4096, seed = 1;
  for (int i = 2; i < argc; i++) {
    if (!strcmp(argv[i], "--pairs")) K = strtoull(argv[++i], 0, 10);
    else if (!strcmp(argv[i], "--heads")) g_heads = 1;
    else if (!strcmp(argv[i], "--seed")) seed = strtoull(argv[++i], 0, 10);
  }
  load_soup(argv[1]);
  Geo g = {0};
  uint8_t a[T2], b[T2];
  uint64_t mismatches = 0;
  for (uint64_t k = 0; k < K; k++) {
    size_t x = sm64(seed * 1000003 + 2 * k) % N, y = sm64(seed * 1000003 + 2 * k + 1) % N;
    if (x == y) y = (y + 1) % N;
    memcpy(a, soup + x * T1, T1); memcpy(a + T1, soup + y * T1, T1);
    memcpy(b, a, T2);
    traced(a, &g);
    evaluate(b, STEP_LIMIT);
    mismatches += memcmp(a, b, T2) != 0;
  }
  uint64_t tot = g.mirror + g.shift + g.other;
  printf("{\"file\":\"%s\",\"heads\":%d,\"pairs\":%llu,\"cross_copies\":%llu,\"mirror\":%llu,\"shift\":%llu,"
         "\"other\":%llu,\"reversed\":%llu,\"forward\":%llu,\"runs_with_copy\":%llu,\"trace_mismatches\":%llu}\n",
         argv[1], g_heads, (unsigned long long)K, (unsigned long long)tot, (unsigned long long)g.mirror,
         (unsigned long long)g.shift, (unsigned long long)g.other, (unsigned long long)g.rev,
         (unsigned long long)g.fwd, (unsigned long long)g.runs_with_copy, (unsigned long long)mismatches);
  return 0;
}
