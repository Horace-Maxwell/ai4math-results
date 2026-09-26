/* closure_replay.c -- regenerates the polynomials h sampled by closure_search.c (same source, same
   seeds, same iteration counts as recorded in the logs), without running the exact tests, and counts
   how many DISTINCT h of each weight each run sampled, and how many are new relative to the runs
   listed before it.  The generator in closure_search.c draws all its random numbers before and
   inside the generation of h; the exact tests draw none, so the sequence of h of a run is determined
   by (m, r, generator variant, seed, number of iterations), and the iteration count is printed at
   the end of every log ("DONE ... iters=N").

   The code between the two marker lines below is copied verbatim from lines 16-75 of
   closure_search.c (SHA-256 d586036889ad77da8d2d177e0911bfed813dcf0236411d378d2ff3e9bb02d4f0);
   the generation loop in main() is copied verbatim from its main().

   Usage: closure_replay m r wlo whi  run1 run2 ...   with run = D:seed:iters (default generator)
          or F:seed:iters (the -DGEN_FLATS generator).  Only h with wlo <= wt h <= whi are counted.
   Build: cc -O2 -o closure_replay closure_replay.c                                             */
/* ---- begin verbatim copy of closure_search.c, lines 16-75 ---- */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define PW 8                       /* projected vector: 8 words = 512 bits */
static int M, R, DD, NPTS, NWT, Dm, FW;
static uint32_t *mono;             /* monomial masks of degree <= DD */
static uint64_t *full;             /* NPTS x FW  full parity-check columns */
static uint64_t *proj;             /* NPTS x PW  projected columns */
static uint64_t X[16][2048];       /* truth tables of coordinate functions (NWT <= 2048 words) */
static uint64_t rs;
/* splitmix64 (nonlinear over F_2; an F_2-linear generator such as xorshift would make the random
   projection below degenerate: all rows would lie in a 64-dimensional subspace) */
static inline uint64_t rnd(void) { uint64_t z = (rs += 0x9E3779B97F4A7C15ULL); z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

static void lin_tt(uint64_t *t, uint32_t u, int b) {   /* t = [u.x == b] */
  for (int w = 0; w < NWT; w++) t[w] = b ? 0 : ~0ULL;
  for (int j = 0; j < M; j++) if (u >> j & 1) for (int w = 0; w < NWT; w++) t[w] ^= X[j][w];
  /* b=0: t = 1 + u.x = [u.x == 0];  b=1: t = u.x = [u.x == 1] */
}
static int rank_vecs(const uint32_t *v, int k) {
  uint32_t b[32] = {0}; int r = 0;
  for (int i = 0; i < k; i++) { uint32_t x = v[i];
    for (int j = 31; j >= 0; j--) { if (!(x >> j & 1)) continue; if (!b[j]) { b[j] = x; r++; break; } x ^= b[j]; } }
  return r;
}
static uint32_t rand_form(void) {       /* structured bias: unit vectors / sums of two units / random */
  int t = rndi(4);
  if (t <= 1) return 1u << rndi(M);
  if (t == 2) { uint32_t u; do { u = (1u << rndi(M)) ^ (1u << rndi(M)); } while (!u); return u; }
  uint32_t u; do { u = (uint32_t)(rnd() & (NPTS - 1)); } while (!u); return u;
}
/* piece: indicator of a flat of codim c (c independent affine equations), times optionally a
   product of `pr` linear forms (pr = 0, 2 or 3), plus optionally a second product term. */
static void piece(uint64_t *t, int c, int pr, int nterms) {
  uint32_t u[20]; int ok;
  do { for (int i = 0; i < c; i++) u[i] = rand_form(); ok = (rank_vecs(u, c) == c); } while (!ok);
  static uint64_t tmp[2048], q[2048], term[2048];
  for (int w = 0; w < NWT; w++) t[w] = ~0ULL;
  for (int i = 0; i < c; i++) { lin_tt(tmp, u[i], rndi(2)); for (int w = 0; w < NWT; w++) t[w] &= tmp[w]; }
  if (pr == 0) return;
  memset(q, 0, sizeof(uint64_t) * NWT);
  for (int s = 0; s < nterms; s++) {
    for (int w = 0; w < NWT; w++) term[w] = ~0ULL;
    for (int i = 0; i < pr; i++) { lin_tt(tmp, rand_form(), rndi(2)); for (int w = 0; w < NWT; w++) term[w] &= tmp[w]; }
    for (int w = 0; w < NWT; w++) q[w] ^= term[w];
  }
  for (int w = 0; w < NWT; w++) t[w] &= q[w];
}
static int popc(const uint64_t *t) { int s = 0; for (int w = 0; w < NWT; w++) s += __builtin_popcountll(t[w]); return s; }
static int anf_deg(const uint64_t *t, int m) {   /* degree of the ANF of a truth table on 2^m points */
  int n = 1 << m; unsigned char *a = malloc(n);
  for (int x = 0; x < n; x++) a[x] = (t[x >> 6] >> (x & 63)) & 1;
  for (int i = 0; i < m; i++) for (int x = 0; x < n; x++) if (x >> i & 1) a[x] ^= a[x ^ (1 << i)];
  int d = -1; for (int x = 0; x < n; x++) if (a[x]) { int k = __builtin_popcount(x); if (k > d) d = k; }
  free(a); return d;
}
/* ---- end verbatim copy ---- */

/* 128-bit fingerprint of a truth table (two independent FNV-style mixes); used as set key */
static void fp(const uint64_t *t, uint64_t *k1, uint64_t *k2) {
  uint64_t a = 0xcbf29ce484222325ULL, b = 0x84222325cbf29ce4ULL;
  for (int w = 0; w < NWT; w++) { a ^= t[w]; a *= 0x100000001b3ULL; a ^= a >> 29;
    b += t[w] * 0x9E3779B97F4A7C15ULL; b ^= b >> 31; b *= 0xBF58476D1CE4E5B9ULL; }
  *k1 = a; *k2 = b;
}
#define HS (1 << 22)
static uint64_t hk1[HS], hk2[HS]; static int hwt[HS], hrun[HS]; static char hused[HS];
/* returns the run index that first inserted this h, or -1 if new (then inserts it) */
static int lookup_insert(uint64_t k1, uint64_t k2, int wt, int run) {
  uint64_t i = (k1 ^ (k2 >> 7)) & (HS - 1);
  while (hused[i]) { if (hk1[i] == k1 && hk2[i] == k2 && hwt[i] == wt) return hrun[i]; i = (i + 1) & (HS - 1); }
  hused[i] = 1; hk1[i] = k1; hk2[i] = k2; hwt[i] = wt; hrun[i] = run; return -1;
}

int main(int argc, char **argv) {
  if (argc < 6) { fprintf(stderr, "usage: m r wlo whi D|F:seed:iters ...\n"); return 1; }
  M = atoi(argv[1]); R = atoi(argv[2]); int wlo = atoi(argv[3]), whi = atoi(argv[4]);
  DD = M - R - 2; NPTS = 1 << M; NWT = NPTS / 64;
  mono = malloc(sizeof(uint32_t) * NPTS); Dm = 0;
  for (uint32_t s = 0; s < (uint32_t)NPTS; s++) if (__builtin_popcount(s) <= DD) mono[Dm++] = s;
  for (int j = 0; j < M; j++) { memset(X[j], 0, sizeof X[j]); for (int x = 0; x < NPTS; x++) if (x >> j & 1) X[j][x >> 6] |= 1ULL << (x & 63); }
  static uint64_t h[2048], t[2048];
  int nruns = argc - 5;
  printf("closure_replay: m=%d r=%d, D=%d parity-check rows, counting %d <= wt h <= %d\n", M, R, Dm, wlo, whi);
  for (int run = 0; run < nruns; run++) {
    char gen; unsigned long long seed; long maxit;
    if (sscanf(argv[5 + run], "%c:%llu:%ld", &gen, &seed, &maxit) != 3) { fprintf(stderr, "bad run spec\n"); return 1; }
    int flats = (gen == 'F');
    rs = seed * 0x9E3779B97F4A7C15ULL + 99;                   /* as in closure_search.c */
    for (int j = 0; j < Dm; j++) for (int w = 0; w < PW; w++) (void)rnd();   /* its projection rho */
    static long samp[70000], newc[70000], earlier[70000], within[70000];
    memset(samp, 0, sizeof samp); memset(newc, 0, sizeof newc); memset(earlier, 0, sizeof earlier); memset(within, 0, sizeof within);
    long iters = 0, first_h_from_run = -2;
    while (iters < maxit) {
      for (int it = 0; it < 256; it++) {
        iters++;
        if (flats) {
          int k = 3 + rndi(2); memset(h, 0, sizeof(uint64_t) * NWT);
          for (int i = 0; i < k; i++) {
            int kind = rndi(16) < 13 ? 0 : 5 + rndi(3), c;
            if (kind == 0) { c = R - (rndi(4) == 0); piece(t, c, 0, 0); for (int w = 0; w < NWT; w++) h[w] ^= t[w]; continue; }
            if (kind <= 4) { c = R - rndi(3); piece(t, c, 0, 0); }
            else if (kind <= 6) { c = R - 2 - rndi(2); if (c < 0) c = 0; piece(t, c, 2, 1 + rndi(3)); }
            else { c = R - 3 - rndi(2); if (c < 0) c = 0; piece(t, c, 3, 1 + rndi(2)); }
            for (int w = 0; w < NWT; w++) h[w] ^= t[w];
          }
        } else {
          int k = 2 + rndi(3); memset(h, 0, sizeof(uint64_t) * NWT);
          for (int i = 0; i < k; i++) {
            int kind = rndi(8), c;
            if (kind <= 4) { c = R - rndi(3); piece(t, c, 0, 0); }
            else if (kind <= 6) { c = R - 2 - rndi(2); if (c < 0) c = 0; piece(t, c, 2, 1 + rndi(3)); }
            else { c = R - 3 - rndi(2); if (c < 0) c = 0; piece(t, c, 3, 1 + rndi(2)); }
            for (int w = 0; w < NWT; w++) h[w] ^= t[w];
          }
        }
        int hw = popc(h);
        if (hw < wlo || hw > whi) continue;
        uint64_t k1, k2; fp(h, &k1, &k2);
        int owner = lookup_insert(k1, k2, hw, run);
        samp[hw]++;
        if (owner < 0) newc[hw]++;             /* first occurrence in any run */
        else if (owner == run) within[hw]++;   /* repeat inside this run */
        else earlier[hw]++;                    /* first sampled by an earlier run */
        if (first_h_from_run == -2) first_h_from_run = (owner < 0) ? -1 : owner;
      }
    }
    printf("run %d  %c seed=%llu iters=%ld (first sampled h in range: %s)\n", run, gen, seed, iters,
           first_h_from_run == -1 ? "new" : "already sampled by an earlier run");
    for (int w = wlo; w <= whi; w++) if (samp[w])
      printf("  wt h=%d: sampled %ld = new %ld + sampled by an earlier run %ld + repeated within this run %ld\n",
             w, samp[w], newc[w], earlier[w], within[w]);
  }
  /* union over all runs */
  static long uni[70000]; memset(uni, 0, sizeof uni);
  for (long i = 0; i < HS; i++) if (hused[i]) uni[hwt[i]]++;
  printf("union over all runs (distinct h):");
  for (int w = wlo; w <= whi; w++) if (uni[w]) printf(" %d:%ld", w, uni[w]);
  printf("\n");
  return 0;
}
