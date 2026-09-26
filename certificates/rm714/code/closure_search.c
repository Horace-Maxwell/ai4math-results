/* closure_search.c -- Task 3 ("inverse" structured search) for weights of RM(r+1, m+1).
   Main run: m = 13, r = 6 (RM(7,14)).  Calibration: m = 11, r = 5 (RM(6,12)).

   Every f in RM(r+1,m+1) is f = g + x_{m+1} h with g in RM(r+1,m), h in RM(r,m), and
       wt f = wt h + 2 |supp g \ supp h|.                                   (PROOF.md, Lemma F3)
   We sample structured h (XOR of 2..4 pieces: affine-flat indicators, flat*quadratic, flat*cubic,
   all of degree <= r) and, for each sampled h, decide EXACTLY whether some g in RM(r+1,m) has
   |supp g \ H| = 1 or = 3 (H = supp h).  With c(x) = (mono(x))_{deg mono <= m-r-2} (the columns of a
   parity-check matrix of RM(r+1,m), whose dual is RM(m-r-2,m)):
       n = 1  <=>  some p notin H has c(p) in span{c(x) : x in H};
       n = 3  <=>  some p,q,s notin H have c(p)+c(q)+c(s) in span{c(x) : x in H}.
   The test is run after a fixed random linear projection F_2^D -> F_2^512.  A linear projection can
   create false positives but never false negatives, so "no hit for this h" is rigorous; every
   positive is re-solved with the full vectors, g is rebuilt, deg g, deg h and wt f are recomputed.
   Usage: closure_search m r seed seconds target_w1 target_w2 ...   (targets = weights of f)      */
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

/* ---- projected RREF basis ---- */
static uint64_t B[600][PW]; static int piv[600]; static int nb;
static void reduce(uint64_t *v) { for (int i = 0; i < nb; i++) if (v[piv[i] >> 6] >> (piv[i] & 63) & 1) for (int w = 0; w < PW; w++) v[w] ^= B[i][w]; }
static void insert(const uint64_t *v0) {
  uint64_t v[PW]; memcpy(v, v0, sizeof v); reduce(v);
  int p = -1; for (int w = 0; w < PW && p < 0; w++) if (v[w]) p = w * 64 + __builtin_ctzll(v[w]);
  if (p < 0) return;
  for (int i = 0; i < nb; i++) if (B[i][p >> 6] >> (p & 63) & 1) for (int w = 0; w < PW; w++) B[i][w] ^= v[w];
  memcpy(B[nb], v, sizeof v); piv[nb] = p; nb++;
}
static inline uint64_t keyof(const uint64_t *v) { uint64_t k = 0; for (int w = 0; w < PW; w++) k ^= (v[w] << (7 * w + 1)) | (v[w] >> (63 - 7 * w)); return k; }

/* ---- exact verification with full vectors and combination tracking ---- */
static int verify(const uint64_t *h, const int *P, int np, int target, long *found_tab) {
  int hw = popc(h);
  int *Hl = malloc(sizeof(int) * hw); int nh = 0;
  for (int x = 0; x < NPTS; x++) if (h[x >> 6] >> (x & 63) & 1) Hl[nh++] = x;
  int CW = (nh + 63) / 64;
  uint64_t *vec = calloc((size_t)(nh + 1) * FW, 8), *cmb = calloc((size_t)(nh + 1) * CW, 8);
  int *pv = malloc(sizeof(int) * (nh + 1)); int nbv = 0;
  for (int i = 0; i < nh; i++) {
    uint64_t *v = vec + (size_t)nbv * FW, *c = cmb + (size_t)nbv * CW;
    memcpy(v, full + (size_t)Hl[i] * FW, 8 * FW); memset(c, 0, 8 * CW); c[i >> 6] |= 1ULL << (i & 63);
    for (int j = 0; j < nbv; j++) if (v[pv[j] >> 6] >> (pv[j] & 63) & 1) {
      for (int w = 0; w < FW; w++) v[w] ^= vec[(size_t)j * FW + w]; for (int w = 0; w < CW; w++) c[w] ^= cmb[(size_t)j * CW + w]; }
    int p = -1; for (int w = 0; w < FW && p < 0; w++) if (v[w]) p = w * 64 + __builtin_ctzll(v[w]);
    if (p < 0) continue;
    for (int j = 0; j < nbv; j++) if (vec[(size_t)j * FW + (p >> 6)] >> (p & 63) & 1) {
      for (int w = 0; w < FW; w++) vec[(size_t)j * FW + w] ^= v[w]; for (int w = 0; w < CW; w++) cmb[(size_t)j * CW + w] ^= c[w]; }
    pv[nbv++] = p;
  }
  uint64_t *t = calloc(FW, 8), *tc = calloc(CW, 8);
  for (int i = 0; i < np; i++) for (int w = 0; w < FW; w++) t[w] ^= full[(size_t)P[i] * FW + w];
  for (int j = 0; j < nbv; j++) if (t[pv[j] >> 6] >> (pv[j] & 63) & 1) {
    for (int w = 0; w < FW; w++) t[w] ^= vec[(size_t)j * FW + w]; for (int w = 0; w < CW; w++) tc[w] ^= cmb[(size_t)j * CW + w]; }
  int zero = 1; for (int w = 0; w < FW; w++) if (t[w]) zero = 0;
  int result = 0;
  if (zero) {
    static uint64_t g[2048]; memset(g, 0, sizeof(uint64_t) * NWT);
    for (int i = 0; i < nh; i++) if (tc[i >> 6] >> (i & 63) & 1) g[Hl[i] >> 6] |= 1ULL << (Hl[i] & 63);
    for (int i = 0; i < np; i++) g[P[i] >> 6] ^= 1ULL << (P[i] & 63);
    int dg = anf_deg(g, M), dh = anf_deg(h, M);
    /* f on 2^(M+1) points: x_{M+1}=0 half is g, =1 half is g+h */
    int NF = NPTS * 2; uint64_t *f = calloc(NF / 64, 8);
    for (int w = 0; w < NWT; w++) { f[w] = g[w]; f[NWT + w] = g[w] ^ h[w]; }
    int wf = 0; for (int w = 0; w < NF / 64; w++) wf += __builtin_popcountll(f[w]);
    int df = anf_deg(f, M + 1);
    int outside = 0; for (int w = 0; w < NWT; w++) outside += __builtin_popcountll(g[w] & ~h[w]);
    int ok = (wf == target && df <= R + 1 && dg <= R + 1 && dh <= R);
    if (!ok || found_tab[target] < 3)
      printf("VERIFIED-HIT target=%d wt_f=%d deg_f=%d deg_g=%d deg_h=%d wt_h=%d |g\\H|=%d ok=%d\n", target, wf, df, dg, dh, hw, outside, ok);
    if (ok) {
      result = 1; found_tab[target]++;
      if (found_tab[target] <= 3) { printf("F_TRUTH_TABLE_HEX");
      for (int w = 0; w < NF / 64; w++) printf(" %016llx", (unsigned long long)f[w]);
      printf("\n"); }
    }
    free(f);
  } else printf("false-positive (projection) target=%d\n", target);
  fflush(stdout);
  free(Hl); free(vec); free(cmb); free(pv); free(t); free(tc);
  return result;
}

int main(int argc, char **argv) {
  M = atoi(argv[1]); R = atoi(argv[2]); rs = strtoull(argv[3], 0, 10) * 0x9E3779B97F4A7C15ULL + 99; double secs = atof(argv[4]);
  int ntg = argc - 5; int tg[32]; for (int i = 0; i < ntg; i++) tg[i] = atoi(argv[5 + i]);
  DD = M - R - 2; NPTS = 1 << M; NWT = NPTS / 64;
  static char istarget[70000]; for (int i = 0; i < ntg; i++) istarget[tg[i]] = 1;
  mono = malloc(sizeof(uint32_t) * NPTS); Dm = 0;
  for (uint32_t s = 0; s < (uint32_t)NPTS; s++) if (__builtin_popcount(s) <= DD) mono[Dm++] = s;
  FW = (Dm + 63) / 64;
  full = calloc((size_t)NPTS * FW, 8); proj = calloc((size_t)NPTS * PW, 8);
  uint64_t (*rho)[PW] = malloc(sizeof(uint64_t) * PW * Dm);
  for (int j = 0; j < Dm; j++) for (int w = 0; w < PW; w++) rho[j][w] = rnd();
  for (int x = 0; x < NPTS; x++) for (int j = 0; j < Dm; j++) if ((mono[j] & (uint32_t)x) == mono[j]) {
    full[(size_t)x * FW + (j >> 6)] |= 1ULL << (j & 63);
    for (int w = 0; w < PW; w++) proj[(size_t)x * PW + w] ^= rho[j][w]; }
  for (int j = 0; j < M; j++) { memset(X[j], 0, sizeof X[j]); for (int x = 0; x < NPTS; x++) if (x >> j & 1) X[j][x >> 6] |= 1ULL << (x & 63); }
  fprintf(stderr, "m=%d r=%d dual degree %d, D=%d\n", M, R, DD, Dm);
  static uint64_t h[2048], t[2048];
  static long tested1[70000], tested3[70000], found[70000], closure_nontriv[70000];
  static uint64_t res[8192][PW]; static uint64_t key[8192]; static int outside[8192];
  static int hk[1 << 15]; static int hn[8192];                 /* hash: head/next lists */
  long iters = 0, rankdef_hist[64] = {0};
#ifdef ZHIST
  static long zhist[70000][16];
#endif
  clock_t t0 = clock();
  while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
    for (int it = 0; it < 256; it++) {
      iters++;
#ifdef GEN_FLATS
      /* variant: 3 or 4 pieces, mostly flats of dimension m-r or m-r+1 (Prop. D / E neighbourhood) */
      int k = 3 + rndi(2); memset(h, 0, sizeof(uint64_t) * NWT);
      for (int i = 0; i < k; i++) {
        int kind = rndi(16) < 13 ? 0 : 5 + rndi(3), c;
        if (kind == 0) { c = R - (rndi(4) == 0); piece(t, c, 0, 0); for (int w = 0; w < NWT; w++) h[w] ^= t[w]; continue; }
#else
      int k = 2 + rndi(3); memset(h, 0, sizeof(uint64_t) * NWT);
      for (int i = 0; i < k; i++) {
        int kind = rndi(8), c;
#endif
        if (kind <= 4) { c = R - rndi(3); piece(t, c, 0, 0); }      /* flat of codim R..R-2, degree <= R */
        else if (kind <= 6) { c = R - 2 - rndi(2); if (c < 0) c = 0; piece(t, c, 2, 1 + rndi(3)); }
        else { c = R - 3 - rndi(2); if (c < 0) c = 0; piece(t, c, 3, 1 + rndi(2)); }
        for (int w = 0; w < NWT; w++) h[w] ^= t[w];
      }
      int hw = popc(h);
      int do1 = (hw + 2 < 70000) && istarget[hw + 2], do3 = (hw + 6 < 70000) && istarget[hw + 6];
      if (!do1 && !do3) continue;
      /* projected basis of H */
      nb = 0;
      for (int x = 0; x < NPTS; x++) if (h[x >> 6] >> (x & 63) & 1) insert(proj + (size_t)x * PW);
      int def = hw - nb; rankdef_hist[def < 63 ? def : 63]++;
      int no = 0;
      for (int x = 0; x < NPTS; x++) if (!(h[x >> 6] >> (x & 63) & 1)) {
        memcpy(res[no], proj + (size_t)x * PW, sizeof res[no]); reduce(res[no]); outside[no] = x; no++; }
#ifdef ZHIST
      { int Zc = 0; for (int i = 0; i < no; i++) { int z = 1; for (int w = 0; w < PW; w++) if (res[i][w]) { z = 0; break; } Zc += z; }
        zhist[hw][Zc < 15 ? Zc : 15]++; }
#endif
      if (do1) {
        tested1[hw + 2]++; int any = 0;
        for (int i = 0; i < no; i++) { int z = 1; for (int w = 0; w < PW; w++) if (res[i][w]) z = 0;
          if (z) { any = 1; int P[1] = {outside[i]}; if (verify(h, P, 1, hw + 2, found)) break; } }
        if (any) closure_nontriv[hw + 2]++;
      }
      if (do3) {
        /* n = 3 <=> (i) >= 3 zero residuals, or (ii) a zero residual and two equal nonzero residuals,
           or (iii) three pairwise distinct nonzero residual VALUES with v1 + v2 = v3.
           Work with the distinct nonzero values only (avoids blow-up on large closures). */
        tested3[hw + 6]++;
        int Z = 0, zp[3] = {0, 0, 0};
        static int uniq[8192], cls[8192], second[8192]; int nu = 0;
        memset(hk, -1, sizeof hk);
        for (int i = 0; i < no; i++) {
          int z = 1; for (int w = 0; w < PW; w++) if (res[i][w]) { z = 0; break; }
          if (z) { if (Z < 3) zp[Z] = i; Z++; continue; }
          uint64_t kk = keyof(res[i]); int b = (int)(kk & ((1 << 15) - 1)), dup = -1;
          for (int s = hk[b]; s >= 0; s = hn[s]) { int u = uniq[s]; if (key[s] != kk) continue;
            int eq = 1; for (int w = 0; w < PW; w++) if (res[u][w] != res[i][w]) { eq = 0; break; }
            if (eq) { dup = s; break; } }
          if (dup >= 0) { cls[dup]++; if (cls[dup] == 2) second[dup] = i; continue; }
          uniq[nu] = i; key[nu] = kk; cls[nu] = 1; hn[nu] = hk[b]; hk[b] = nu; nu++;
        }
        if (Z >= 3) { int P[3] = {outside[zp[0]], outside[zp[1]], outside[zp[2]]}; if (verify(h, P, 3, hw + 6, found)) goto done3; }
        if (Z >= 1) for (int a2 = 0; a2 < nu; a2++) if (cls[a2] >= 2) {
          int P[3] = {outside[zp[0]], outside[uniq[a2]], outside[second[a2]]}; if (verify(h, P, 3, hw + 6, found)) goto done3; }
        for (int a = 0; a < nu; a++) for (int c2 = a + 1; c2 < nu; c2++) {
          uint64_t kk = key[a] ^ key[c2]; int b = (int)(kk & ((1 << 15) - 1));
          for (int s = hk[b]; s >= 0; s = hn[s]) {
            if (s == a || s == c2 || key[s] != kk) continue;
            int ia = uniq[a], ib = uniq[c2], is = uniq[s];
            int eq = 1; for (int w = 0; w < PW; w++) if ((res[ia][w] ^ res[ib][w]) != res[is][w]) { eq = 0; break; }
            if (!eq) continue;
            int P[3] = {outside[ia], outside[ib], outside[is]};
            if (verify(h, P, 3, hw + 6, found)) goto done3;
          }
        }
        done3: ;
      }
    }
  }
  printf("DONE m=%d r=%d iters=%ld\n", M, R, iters);
  for (int i = 0; i < ntg; i++) printf("target %d: h tested for n=1: %ld (nontrivial closure %ld), h tested for n=3: %ld, VERIFIED HITS: %ld\n",
      tg[i], tested1[tg[i]], closure_nontriv[tg[i]], tested3[tg[i]], found[tg[i]]);
#ifdef ZHIST
  for (int w = 0; w < 70000; w++) { long tot = 0; for (int z = 0; z < 16; z++) tot += zhist[w][z]; if (!tot) continue;
    printf("closure size |cl(H)\\H| histogram for wt h=%d:", w); for (int z = 0; z < 16; z++) if (zhist[w][z]) printf(" %d:%ld", z, zhist[w][z]); printf("\n"); }
#endif
  printf("rank deficiency |H|-rank histogram (tested h):"); for (int d = 0; d < 64; d++) if (rankdef_hist[d]) printf(" %d:%ld", d, rankdef_hist[d]); printf("\n");
  return 0;
}
