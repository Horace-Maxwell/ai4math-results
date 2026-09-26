/*
 * Independent check (no networkx, no scout code) for HKO (arXiv:2103.10806) Problems 1-2.
 *
 * For every labeled simple graph on n vertices (n = 1..NMAX), i.e. every subset of the
 * n(n-1)/2 possible edges:
 *   - keep it if connected (bitmask BFS);
 *   - distances by bitmask BFS;
 *   - median test, standard definition (Mulder 1978, as quoted in HKO Sec. 2):
 *       |[u,v] ∩ [u,w] ∩ [v,w]| = 1 for ALL triples u,v,w (repetitions allowed),
 *       [u,v] = {x : d(u,x)+d(x,v) = d(u,v)};
 *   - tr(G) = max over ALL ordered triples (repetitions allowed) of d(a,b)+d(a,c)+d(b,c);
 *   - diam, peripheral (ecc(v) = diam), Q3' (every triametral triple, repetitions allowed,
 *     contains a peripheral vertex), Q4 (every diametral pair {x,y} has z, ANY z, with
 *     d(x,y,z) = tr), Q4dist (same with z required distinct from x,y), Q3 (every triametral
 *     triple contains a diametral pair).
 *   - canonical form of median graphs = lexicographically minimal edge mask over all n!
 *     relabelings (n <= 7), to count isomorphism classes.
 * For n = 8 (optional, argv[2] = 1) no full canonical forms are computed; violators are
 * reported with an invariant-refined canonical form (permutations within invariant cells).
 *
 * Usage: ./median_enum NMAX [do8]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 8
static int n;
static int eu[28], ev[28], ne;
static int adj[MAXN];
static int d[MAXN][MAXN];

static void setup_edges(void) {
  ne = 0;
  for (int i = 0; i < n; i++)
    for (int j = i + 1; j < n; j++) { eu[ne] = i; ev[ne] = j; ne++; }
}

static void build(uint32_t mask) {
  for (int i = 0; i < n; i++) adj[i] = 0;
  for (int e = 0; e < ne; e++)
    if (mask >> e & 1) { adj[eu[e]] |= 1 << ev[e]; adj[ev[e]] |= 1 << eu[e]; }
}

/* returns 1 if connected, fills d */
static int distances(void) {
  int full = (1 << n) - 1;
  for (int s = 0; s < n; s++) {
    int seen = 1 << s, frontier = 1 << s, k = 0;
    for (int t = 0; t < n; t++) d[s][t] = -1;
    d[s][s] = 0;
    while (frontier) {
      int nxt = 0;
      for (int v = 0; v < n; v++) if (frontier >> v & 1) nxt |= adj[v];
      nxt &= ~seen;
      k++;
      for (int v = 0; v < n; v++) if (nxt >> v & 1) d[s][v] = k;
      seen |= nxt;
      frontier = nxt;
    }
    if (seen != full) return 0;
  }
  return 1;
}

static int connected_quick(void) {
  int seen = 1, frontier = 1, full = (1 << n) - 1;
  while (frontier) {
    int nxt = 0;
    for (int v = 0; v < n; v++) if (frontier >> v & 1) nxt |= adj[v];
    nxt &= ~seen; seen |= nxt; frontier = nxt;
  }
  return seen == full;
}

/* A triangle a,b,c gives [a,b]={a,b}, [a,c]={a,c}, [b,c]={b,c} with empty intersection, so a
   graph with a triangle fails the median definition; this filter only skips work. */
static int has_triangle(void) {
  for (int e = 0; e < ne; e++)
    if ((adj[eu[e]] >> ev[e] & 1) && (adj[eu[e]] & adj[ev[e]])) return 1;
  return 0;
}

static int is_median(void) {
  for (int u = 0; u < n; u++)
    for (int v = 0; v < n; v++)
      for (int w = 0; w < n; w++) {
        int cnt = 0;
        for (int x = 0; x < n; x++)
          if (d[u][x] + d[x][v] == d[u][v] && d[u][x] + d[x][w] == d[u][w] &&
              d[v][x] + d[x][w] == d[v][w]) cnt++;
        if (cnt != 1) return 0;
      }
  return 1;
}

typedef struct { int diam, tr, per, q3p, q4, q4dist, q3; int bad3p[3]; int bad4[2]; } Props;

static Props props(void) {
  Props p; memset(&p, 0, sizeof p);
  int ecc[MAXN];
  p.diam = 0;
  for (int u = 0; u < n; u++) {
    ecc[u] = 0;
    for (int v = 0; v < n; v++) if (d[u][v] > ecc[u]) ecc[u] = d[u][v];
    if (ecc[u] > p.diam) p.diam = ecc[u];
  }
  p.per = 0;
  for (int u = 0; u < n; u++) if (ecc[u] == p.diam) p.per |= 1 << u;
  p.tr = 0;
  for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) for (int c = 0; c < n; c++) {
    int s = d[a][b] + d[a][c] + d[b][c];
    if (s > p.tr) p.tr = s;
  }
  p.q3p = 1; p.q3 = 1; p.bad3p[0] = -1;
  for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) for (int c = 0; c < n; c++) {
    if (d[a][b] + d[a][c] + d[b][c] != p.tr) continue;
    if (!((p.per >> a & 1) || (p.per >> b & 1) || (p.per >> c & 1))) {
      if (p.q3p) { p.bad3p[0] = a; p.bad3p[1] = b; p.bad3p[2] = c; }
      p.q3p = 0;
    }
    if (!(d[a][b] == p.diam || d[a][c] == p.diam || d[b][c] == p.diam)) p.q3 = 0;
  }
  p.q4 = 1; p.q4dist = 1; p.bad4[0] = -1;
  for (int x = 0; x < n; x++) for (int y = 0; y < n; y++) {
    if (d[x][y] != p.diam) continue;
    int ok = 0, okd = 0;
    for (int z = 0; z < n; z++) {
      if (d[x][y] + d[x][z] + d[y][z] == p.tr) { ok = 1; if (z != x && z != y) okd = 1; }
    }
    if (!ok) { if (p.q4) { p.bad4[0] = x; p.bad4[1] = y; } p.q4 = 0; }
    if (!okd) p.q4dist = 0;
  }
  return p;
}

/* canonical form: min over all permutations of relabeled edge mask (n <= 7) */
static int perm[MAXN];
static uint32_t best;
static int pairidx[MAXN][MAXN];
static void canon_rec(int k, int used, uint32_t mask) {
  if (k == n) {
    uint32_t m = 0;
    for (int e = 0; e < ne; e++)
      if (mask >> e & 1) m |= 1u << pairidx[perm[eu[e]]][perm[ev[e]]];
    if (m < best) best = m;
    return;
  }
  for (int v = 0; v < n; v++) if (!(used >> v & 1)) { perm[k] = v; canon_rec(k + 1, used | 1 << v, mask); }
}
static uint32_t canon_full(uint32_t mask) { best = 0xFFFFFFFFu; canon_rec(0, 0, mask); return best; }

/* invariant-refined canonical form: vertices sorted by invariant; permute within cells only */
static long inv[MAXN];
static int order[MAXN];
static int cellstart[MAXN], cellend[MAXN];
static void cell_rec(int pos, int used, uint32_t mask, int *pl /* position->vertex */) {
  if (pos == n) {
    int lab[MAXN];
    for (int i = 0; i < n; i++) lab[pl[i]] = i;
    uint32_t m = 0;
    for (int e = 0; e < ne; e++)
      if (mask >> e & 1) m |= 1u << pairidx[lab[eu[e]]][lab[ev[e]]];
    if (m < best) best = m;
    return;
  }
  for (int i = cellstart[pos]; i < cellend[pos]; i++) {
    int v = order[i];
    if (used >> v & 1) continue;
    pl[pos] = v;
    cell_rec(pos + 1, used | 1 << v, mask, pl);
  }
}
static uint32_t canon_refined(uint32_t mask) {
  /* invariant: (degree, distance profile) */
  for (int v = 0; v < n; v++) {
    long x = __builtin_popcount(adj[v]);
    int prof[MAXN] = {0};
    for (int u = 0; u < n; u++) prof[d[v][u]]++;
    for (int k = 0; k < n; k++) x = x * 9 + prof[k];
    inv[v] = x;
  }
  for (int i = 0; i < n; i++) order[i] = i;
  for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++)
    if (inv[order[j]] < inv[order[i]]) { int t = order[i]; order[i] = order[j]; order[j] = t; }
  for (int i = 0; i < n; ) {
    int j = i; while (j < n && inv[order[j]] == inv[order[i]]) j++;
    for (int k = i; k < j; k++) { cellstart[k] = i; cellend[k] = j; }
    i = j;
  }
  int pl[MAXN];
  best = 0xFFFFFFFFu;
  cell_rec(0, 0, mask, pl);
  return best;
}

static int cmp_u32(const void *a, const void *b) {
  uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b; return x < y ? -1 : x > y;
}
static size_t uniq(uint32_t *a, size_t m) {
  if (!m) return 0;
  qsort(a, m, sizeof *a, cmp_u32);
  size_t k = 1;
  for (size_t i = 1; i < m; i++) if (a[i] != a[k - 1]) a[k++] = a[i];
  return k;
}

static void print_graph(uint32_t mask) {
  printf("edges:");
  for (int e = 0; e < ne; e++) if (mask >> e & 1) printf(" %d-%d", eu[e], ev[e]);
}

int main(int argc, char **argv) {
  int nmax = argc > 1 ? atoi(argv[1]) : 7;
  int do8 = argc > 2 ? atoi(argv[2]) : 0;
  for (n = 1; n <= nmax; n++) {
    setup_edges();
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) pairidx[i][j] = -1;
    for (int e = 0; e < ne; e++) { pairidx[eu[e]][ev[e]] = e; pairidx[ev[e]][eu[e]] = e; }
    uint64_t total = 1ull << ne, conn = 0, med = 0;
    uint64_t f3p = 0, f4 = 0, f4d = 0, f3 = 0;
    size_t cap = 1 << 22, m = 0, mr = 0, mv3 = 0, mv4 = 0;
    uint32_t *cf = malloc(cap * sizeof *cf), *cr = malloc(cap * sizeof *cr);
    uint32_t *v3 = malloc(cap * sizeof *v3), *v4 = malloc(cap * sizeof *v4);
    for (uint64_t mask = 0; mask < total; mask++) {
      build((uint32_t)mask);
      if (!connected_quick()) continue;
      conn++;
      if (has_triangle()) continue;
      if (!distances()) { fprintf(stderr, "inconsistent connectivity\n"); return 1; }
      if (!is_median()) continue;
      med++;
      Props p = props();
      if (!p.q3p) f3p++;
      if (!p.q4) f4++;
      if (!p.q4dist) f4d++;
      if (!p.q3) f3++;
      if (n <= 7) {
        if (m == cap) { fprintf(stderr, "cap\n"); return 1; }
        cf[m++] = canon_full((uint32_t)mask);
      }
      if (mr < cap) cr[mr++] = canon_refined((uint32_t)mask);
      if (!p.q3p && mv3 < cap) v3[mv3++] = canon_refined((uint32_t)mask);
      if (!p.q4 && mv4 < cap) v4[mv4++] = canon_refined((uint32_t)mask);
    }
    size_t kf = n <= 7 ? uniq(cf, m) : 0, kr = uniq(cr, mr);
    size_t k3 = uniq(v3, mv3), k4 = uniq(v4, mv4);
    printf("n=%d labeled_graphs=%llu connected=%llu median_labeled=%llu "
           "iso_classes_fullcanon=%zu iso_classes_refinedcanon=%zu "
           "Q3'_fail_labeled=%llu Q4_fail_labeled=%llu Q4distinctz_fail_labeled=%llu Q3_fail_labeled=%llu "
           "Q3'_fail_iso=%zu Q4_fail_iso=%zu\n",
           n, (unsigned long long)total, (unsigned long long)conn, (unsigned long long)med, kf, kr,
           (unsigned long long)f3p, (unsigned long long)f4, (unsigned long long)f4d,
           (unsigned long long)f3, k3, k4);
    for (size_t i = 0; i < k3; i++) {
      build(v3[i]); distances(); Props p = props();
      printf("  Q3'-violator (canonical) "); print_graph(v3[i]);
      printf(" | diam=%d tr=%d bad_triple=(%d,%d,%d)\n", p.diam, p.tr, p.bad3p[0], p.bad3p[1], p.bad3p[2]);
    }
    for (size_t i = 0; i < k4; i++) {
      build(v4[i]); distances(); Props p = props();
      printf("  Q4-violator (canonical) "); print_graph(v4[i]);
      printf(" | diam=%d tr=%d bad_pair=(%d,%d)\n", p.diam, p.tr, p.bad4[0], p.bad4[1]);
    }
    fflush(stdout);
    free(cf); free(cr); free(v3); free(v4);
    if (n == 7 && !do8) break;
  }
  return 0;
}
