/* Exhaustive exact search for max energy of ICG(p^a q^b, D) over nonempty
 * proper-divisor sets D, using E = || T_a(p) X T_b(q)^T ||_1 (exact int64).
 * Usage: icg_search a b p q nprefixbits prefix_lo prefix_hi
 * Enumerates masks whose top `nprefixbits` bits lie in [prefix_lo, prefix_hi).
 * Bits: cells (i,j) != (a,b) in row-major order, bit t <-> cell t.
 * Prints the top-K (energy, mask) list for the range (mask 0 = empty set skipped).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define MAXD 16
#define TOPK 12
#ifndef SIGNMODE
#define SIGNMODE 0
#endif
#define SC (SIGNMODE ? 2 : 1)
typedef long long ll;

static ll M[MAXD][MAXD], N[MAXD][MAXD];
static int A, B, NC; /* NC = number of cells (bits) */
static int ci[MAXD * MAXD], cj[MAXD * MAXD];

static ll ipow(ll x, int e) { ll r = 1; while (e--) r *= x; return r; }
static ll phi_pp(ll x, int e) { return e == 0 ? 1 : ipow(x, e - 1) * (x - 1); }
static ll ram_pp(ll x, int k, int i) {
  if (k == 0) return 1;
  if (k <= i) return ipow(x, k - 1) * (x - 1);
  if (k == i + 1) return -ipow(x, k - 1);
  return 0;
}
static void buildT(ll T[MAXD][MAXD], int k, ll x) {
  for (int i = 0; i <= k; i++)
    for (int j = 0; j <= k; j++) T[i][j] = phi_pp(x, k - i) * ram_pp(x, k - j, i);
}

static ll topE[TOPK]; static unsigned long long topM[TOPK]; static int ntop = 0;
static void push(ll e, unsigned long long m) {
  if (ntop == TOPK && e <= topE[TOPK - 1]) return;
  int pos = (ntop < TOPK) ? ntop++ : TOPK - 1;
  topE[pos] = e; topM[pos] = m;
  while (pos > 0 && topE[pos] > topE[pos - 1]) {
    ll te = topE[pos]; topE[pos] = topE[pos - 1]; topE[pos - 1] = te;
    unsigned long long tm = topM[pos]; topM[pos] = topM[pos - 1]; topM[pos - 1] = tm;
    pos--;
  }
}

int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "usage\n"); return 1; }
  A = atoi(argv[1]); B = atoi(argv[2]);
  ll p = atoll(argv[3]), q = atoll(argv[4]);
  int PB = atoi(argv[5]);
  unsigned long long lo = strtoull(argv[6], 0, 10), hi = strtoull(argv[7], 0, 10);
  buildT(M, A, p); buildT(N, B, q);
  NC = 0;
  for (int i = 0; i <= A; i++) for (int j = 0; j <= B; j++) if (!(i == A && j == B) || SIGNMODE) { ci[NC] = i; cj[NC] = j; NC++; }
  int LB = NC - PB; /* low bits enumerated by Gray code */
  static ll Z[MAXD][MAXD];
  unsigned long long visited = 0, esum = 0;
  for (unsigned long long pre = lo; pre < hi; pre++) {
    /* initial mask: prefix in top bits, low bits zero */
    unsigned long long mask = pre << LB;
    memset(Z, 0, sizeof Z);
    if (SIGNMODE) Z[A][B] = -ipow(p, A) * ipow(q, B);
    for (int t = 0; t < NC; t++) if (mask >> t & 1) {
      int i = ci[t], j = cj[t];
      for (int u = 0; u <= A; u++) if (M[u][i]) for (int v = 0; v <= B; v++) Z[u][v] += SC * M[u][i] * N[v][j];
    }
    ll E = 0; for (int u = 0; u <= A; u++) for (int v = 0; v <= B; v++) E += llabs(Z[u][v]);
    if (mask || SIGNMODE) push(E, mask);
    visited++; esum += (unsigned long long)E;
    unsigned long long cnt = 1ULL << LB;
    for (unsigned long long k = 1; k < cnt; k++) {
      int t = __builtin_ctzll(k);
      int i = ci[t], j = cj[t];
      int sgn = (mask >> t & 1) ? -1 : 1;
      mask ^= 1ULL << t;
      for (int u = 0; u <= A; u++) {
        ll mu = M[u][i]; if (!mu) continue; mu *= sgn * SC;
        for (int v = 0; v <= B; v++) {
          ll nv = N[v][j]; if (!nv) continue;
          ll old = Z[u][v], nw = old + mu * nv;
          E += llabs(nw) - llabs(old); Z[u][v] = nw;
        }
      }
      push(E, mask);
      visited++; esum += (unsigned long long)E;
    }
  }
  for (int t = 0; t < ntop; t++) printf("%lld %llu\n", topE[t], topM[t]);
  fprintf(stderr, "visited %llu esum %llu\n", visited, esum);
  return 0;
}
