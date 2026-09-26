/*
 * sunD.c -- implementation D, written from scratch by the paper-7 referee (2026-09-26).
 *
 * Graphs: cycle C_b (b even), vertex k carries p_k pendant vertices and q_k pendant P_2's
 * (both kinds allowed at one vertex).  n = b + sum(p_k + 2 q_k) <= N.
 *
 * Enumeration (different from A, B, C):
 *   plain DFS over ALL sequences ((p_k,q_k))_{k=0..b-1}, no rotation filter; the only
 *   pruning is EXACT reachability of the 2nd/4th-moment identities, via a DP table
 *   R[r][w] = set of values sum_{j} c(p_j,q_j) over r vertices of total weight w,
 *   c(p,q) = (2+p+q)(1+p+q) + 2q  (the vertex's share of sum_v d_v(d_v-1)).
 *   A node is expanded iff some completion satisfies Theta + 4[b=4] = T(B+) and
 *   S2(B+) <= n <= N for an admissible multiset B+ of eigenvalues >= 2.
 *   Admissible B+ (b even, G bipartite, connected, properly containing C_b):
 *     max element rho >= 3, simple (Perron-Frobenius); other elements in [2,rho-1],
 *     each at most twice (cycle recurrence has a 2-dim solution space); S2 <= N.
 *   Moment identities for integral bipartite G: sum_{B+} l^2 = n - mult(1) <= n,
 *     sum_{B+} l^2 (l^2 - 1) = Theta + 4 c_4  (tr A^4 - tr A^2 = 2 Theta + 8 c_4).
 *   Optional: canonical = least image under the dihedral group (mode "canon").
 *
 * Exact test (different from A, B, C): for every integer k in [-9,9] an upper bound
 *   nu_k >= mult(k) is computed as a nullity over GF(2^31-1) of a b x b matrix:
 *     |k| >= 2:  M = k(k^2-1)(A(C_b) - kI) + diag(p_j(k^2-1) + q_j k^2)     (Schur complement)
 *     k = 0:     sum_{p_j>0}(p_j-1) + nullity E0,  E0 row j = e_j if p_j>0, else e_{j-1}+e_{j+1}
 *     k = e=+-1: sum_{q_j>0}(q_j-1) + nullity Ee,  Ee row j = e_j if q_j>0,
 *                                                  else e_{j-1}+e_{j+1}+e(p_j-1)e_j
 *   rank over GF(P) <= rank over Q, so nu_k >= mult(k).  All eigenvalues satisfy
 *   |l| <= sqrt(2n) < 10.  Hence sum_k nu_k < n  ==>  G not integral (certified).
 *   Leaves with sum_k nu_k >= n are printed as CAND and confirmed separately with SymPy.
 *
 * v2 additions (all optional flags; each is a proved necessary condition):
 *   load:  mult(1) = n - S2 <= max(Q,2)  (at most one free parameter per gap of K_q, or a
 *          2-dim cyclic recurrence if K_q is empty; plus q_j - 1 per vertex) -- always on in v2;
 *   l6:    |B+| >= N_{>1}(C_b)  (Cauchy interlacing with the induced cycle);
 *   wmax:  orderly generation: w_0 = max_k w_k (w = p + 2q); canonical leaf = greatest image
 *          under the key 64*w + p.
 * Usage: sunD2 b N part nparts {all|canon} [dry] [l6] [wmax]
 *        sunD test   (stdin: "b p0 q0 ... ; prints n and nu_{-9..9}")
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXB 16
#define MAXW 64
#define WORDS 48            /* bitset over Theta values 0 .. 64*WORDS-1 = 3071 */
#define MAXT (64*WORDS)
typedef uint64_t u64;
static const u64 PMOD = 2147483647ULL;

static int b, N, WMAX, QMAX, part, nparts, canon, dry, use_l6, use_wmax, noprune;
static int adj4;
static int nspec; static int specT[512], specS2[512];
#define MAXQ 24
static u64 R[MAXB + 1][MAXW + 1][MAXQ + 1][WORDS];
static u64 SU[MAXB + 1][MAXW + 1][MAXQ + 2][WORDS];
static u64 F[MAXB + 1][MAXW + 1][MAXQ + 1][WORDS];
static int P_[MAXB], Q_[MAXB];
static long long leaves = 0, tested = 0, cands = 0, nodes = 0, splitctr = 0;

static inline int cval(int p, int q) { return (2 + p + q) * (1 + p + q) + 2 * q; }
static inline int getbit(const u64 *s, int i) { return (i >= 0 && i < MAXT) ? (int)((s[i >> 6] >> (i & 63)) & 1) : 0; }
static inline void setbit(u64 *s, int i) { if (i >= 0 && i < MAXT) s[i >> 6] |= 1ULL << (i & 63); }

static void gen_spectra(void) {
    nspec = 0;
    int m[10];
    for (int rho = 3; rho <= 9; rho++) {
        if (rho * rho > N) break;
        int lim = 1; for (int v = 2; v < rho; v++) lim *= 3;
        for (int code = 0; code < lim; code++) {
            int t = code; for (int v = 2; v < rho; v++) { m[v] = t % 3; t /= 3; }
            int S2 = rho * rho, T = rho * rho * (rho * rho - 1);
            for (int v = 2; v < rho; v++) { S2 += m[v] * v * v; T += m[v] * v * v * (v * v - 1); }
            if (S2 > N) continue;
            int card = 1; for (int v = 2; v < rho; v++) card += m[v];
            if (use_l6) {
                int c1 = 0;
                for (int j = 0; j < b; j++) { int jj = j; if (2 * jj > b) jj -= b; if (jj < 0) jj = -jj; if (6 * jj < b) c1++; }
                if (card < c1) continue;
            }
            specT[nspec] = T; specS2[nspec] = S2; nspec++;
        }
    }
}

static void shift_or(u64 *dst, const u64 *src, int sh) {   /* dst |= src << sh (bits >= MAXT dropped) */
    int ws = sh >> 6, bs = sh & 63;
    for (int i = WORDS - 1; i >= ws; i--) {
        u64 v = src[i - ws] << bs;
        if (bs && i - ws - 1 >= 0) v |= src[i - ws - 1] >> (64 - bs);
        dst[i] |= v;
    }
}

static void build_tables(void) {
    memset(R, 0, sizeof R); memset(SU, 0, sizeof SU); memset(F, 0, sizeof F);
    setbit(R[0][0][0], 0);
    for (int r = 1; r <= b; r++)
        for (int w = 0; w <= WMAX; w++)
            for (int Qr = 0; Qr <= QMAX && 2 * Qr <= w; Qr++)
                for (int q = 0; q <= Qr; q++)
                    for (int p = 0; p + 2 * q <= w; p++) {
                        int c = cval(p, q); if (c >= MAXT) break;
                        shift_or(R[r][w][Qr], R[r - 1][w - p - 2 * q][Qr - q], c);
                    }
    for (int r = 0; r <= b; r++)
        for (int w = 0; w <= WMAX; w++)
            for (int Qlo = QMAX; Qlo >= 0; Qlo--)
                for (int i = 0; i < WORDS; i++) SU[r][w][Qlo][i] = SU[r][w][Qlo + 1][i] | R[r][w][Qlo][i];
    /* F[r][W][Qu]: Theta values after assigning b-r vertices (weight W, sum of q = Qu) that admit
       a completion by r vertices (weight wr, sum of q = Qr) and an admissible (T,S2) with
       Theta_total + adj4 = T, S2 <= n <= N, n - max(Qu+Qr, 2) <= S2. */
    for (int r = 0; r <= b; r++)
        for (int W = 0; W <= WMAX; W++)
            for (int Qu = 0; Qu <= QMAX && 2 * Qu <= W; Qu++)
                for (int s = 0; s < nspec; s++) {
                    u64 U[WORDS]; memset(U, 0, sizeof U);
                    for (int wr = 0; W + wr <= WMAX; wr++) {
                        int n = b + W + wr;
                        if (n < specS2[s]) continue;
                        int Qlo = 0;
                        if (n - 2 > specS2[s]) { Qlo = n - specS2[s] - Qu; if (Qlo < 0) Qlo = 0; }
                        if (Qlo > QMAX) continue;
                        for (int i = 0; i < WORDS; i++) U[i] |= SU[r][wr][Qlo][i];
                    }
                    int T = specT[s] - adj4;
                    for (int x = 0; x <= T && x < MAXT; x++)
                        if (getbit(U, x)) setbit(F[r][W][Qu], T - x);
                }
}

/* ---------- exact-test helpers: nullity over GF(PMOD) ---------- */
static u64 inv_mod(u64 a) {
    long long t = 0, nt = 1, r = (long long)PMOD, nr = (long long)(a % PMOD);
    while (nr) { long long qq = r / nr, tmp; tmp = t - qq * nt; t = nt; nt = tmp; tmp = r - qq * nr; r = nr; nr = tmp; }
    if (t < 0) t += (long long)PMOD;
    return (u64)t;
}
static inline u64 md(long long x) { long long r = x % (long long)PMOD; if (r < 0) r += (long long)PMOD; return (u64)r; }
static int nullity(u64 M[MAXB][MAXB], int n) {
    int rank = 0;
    for (int col = 0; col < n && rank < n; col++) {
        int piv = -1;
        for (int i = rank; i < n; i++) if (M[i][col]) { piv = i; break; }
        if (piv < 0) continue;
        if (piv != rank) for (int j = 0; j < n; j++) { u64 t = M[piv][j]; M[piv][j] = M[rank][j]; M[rank][j] = t; }
        u64 iv = inv_mod(M[rank][col]);
        for (int i = rank + 1; i < n; i++) if (M[i][col]) {
            u64 f = (M[i][col] * iv) % PMOD;
            for (int j = col; j < n; j++) if (M[rank][j]) {
                M[i][j] = (M[i][j] + PMOD - (f * M[rank][j]) % PMOD) % PMOD;
            }
        }
        rank++;
    }
    return n - rank;
}
static void nus(const int *p, const int *q, int bb, int nu[19]) {
    u64 M[MAXB][MAXB];
    for (int k = -9; k <= 9; k++) {
        memset(M, 0, sizeof M);
        int extra = 0;
        if (k >= 2 || k <= -2) {
            long long h = (long long)k * (k * k - 1);
            for (int j = 0; j < bb; j++) {
                M[j][(j + 1) % bb] = md(h); M[j][(j + bb - 1) % bb] = md(h);
                M[j][j] = md(-h * k + (long long)p[j] * (k * k - 1) + (long long)q[j] * k * k);
            }
        } else if (k == 0) {
            for (int j = 0; j < bb; j++) {
                if (p[j] > 0) { M[j][j] = 1; extra += p[j] - 1; }
                else { M[j][(j + 1) % bb] = 1; M[j][(j + bb - 1) % bb] = 1; }
            }
        } else {
            for (int j = 0; j < bb; j++) {
                if (q[j] > 0) { M[j][j] = 1; extra += q[j] - 1; }
                else { M[j][(j + 1) % bb] = 1; M[j][(j + bb - 1) % bb] = 1; M[j][j] = md((long long)k * (p[j] - 1)); }
            }
        }
        nu[k + 9] = extra + nullity(M, bb);
    }
}

static int is_canonical(void) {
    int e[MAXB];
    for (int k = 0; k < b; k++) e[k] = use_wmax ? -((P_[k] + 2 * Q_[k]) * 64 + P_[k]) : P_[k] * 64 + Q_[k];
    /* least image of e (= greatest image of the positive key when wmax) */
    for (int s = 0; s < b; s++)
        for (int refl = 0; refl < 2; refl++) {
            if (s == 0 && !refl) continue;
            for (int k = 0; k < b; k++) {
                int idx = refl ? ((s - k) % b + b) % b : (s + k) % b;
                if (e[idx] < e[k]) return 0;
                if (e[idx] > e[k]) break;
            }
        }
    return 1;
}

static void leaf(int W) {
    leaves++;
    if (dry) return;
    if (canon && !is_canonical()) return;
    tested++;
    int n = b + W, nu[19], s = 0;
    nus(P_, Q_, b, nu);
    for (int i = 0; i < 19; i++) s += nu[i];
    if (s >= n) {
        cands++;
        printf("CAND b=%d n=%d :", b, n);
        for (int k = 0; k < b; k++) printf(" (%d,%d)", P_[k], Q_[k]);
        printf("  nu:");
        for (int i = 0; i < 19; i++) if (nu[i]) printf(" %d^%d", i - 9, nu[i]);
        printf("\n"); fflush(stdout);
    }
}

static void dfs(int k, int theta, int W, int Qu) {
    nodes++;
    if (k == b) { if (W > 0) leaf(W); return; }   /* the bare cycle is excluded */
    if (k == 2) { long long c = splitctr++; if (c % nparts != part) return; }
    int r = b - k - 1;
    int wcap = WMAX - W;
    if (use_wmax && k >= 1 && P_[0] + 2 * Q_[0] < wcap) wcap = P_[0] + 2 * Q_[0];
    for (int p = 0; p <= wcap; p++) {
        if (theta + cval(p, 0) >= MAXT) break;
        for (int q = 0; p + 2 * q <= wcap; q++) {
            int th = theta + cval(p, q);
            if (th >= MAXT) break;
            int W2 = W + p + 2 * q, Q2 = Qu + q;
            if (Q2 > QMAX) break;
            if (!noprune && !getbit(F[r][W2][Q2], th)) continue;
            P_[k] = p; Q_[k] = q;
            dfs(k + 1, th, W2, Q2);
        }
    }
}

int main(int argc, char **argv) {
    if (argc >= 2 && !strcmp(argv[1], "test")) {
        int bb; int p[MAXB], q[MAXB], nu[19];
        while (scanf("%d", &bb) == 1) {
            int n = bb;
            for (int k = 0; k < bb; k++) { if (scanf("%d %d", &p[k], &q[k]) != 2) return 1; n += p[k] + 2 * q[k]; }
            nus(p, q, bb, nu);
            printf("%d", n); for (int i = 0; i < 19; i++) printf(" %d", nu[i]); printf("\n");
        }
        return 0;
    }
    if (argc < 6) { fprintf(stderr, "usage: sunD b N part nparts {all|canon} [dry]\n"); return 1; }
    b = atoi(argv[1]); N = atoi(argv[2]); part = atoi(argv[3]); nparts = atoi(argv[4]);
    canon = !strcmp(argv[5], "canon");
    for (int i = 6; i < argc; i++) {
        if (!strcmp(argv[i], "dry")) dry = 1;
        else if (!strcmp(argv[i], "l6")) use_l6 = 1;
        else if (!strcmp(argv[i], "wmax")) use_wmax = 1;
        else if (!strcmp(argv[i], "np")) noprune = 1;
        else { fprintf(stderr, "unknown flag %s\n", argv[i]); return 1; }
    }
    for (int i = 6; i < argc; i++) if (!strcmp(argv[i], "np")) noprune = 1;
    if ((b % 2 && !noprune) || b < 3 || b > MAXB || N - b > MAXW || N > 49) { fprintf(stderr, "bad b/N (odd b only with np)\n"); return 1; }
    WMAX = N - b; QMAX = WMAX / 2; if (QMAX > MAXQ) { fprintf(stderr, "QMAX\n"); return 1; }
    adj4 = (b == 4) ? 4 : 0;
    gen_spectra();
    int maxT = 0; for (int s = 0; s < nspec; s++) if (specT[s] > maxT) maxT = specT[s];
    if (maxT + 8 >= MAXT) { fprintf(stderr, "MAXT too small\n"); return 1; }
    fprintf(stderr, "sunD2 b=%d N=%d part=%d/%d mode=%s%s%s%s spectra=%d maxT=%d\n", b, N, part, nparts,
            canon ? "canon" : "all", dry ? " dry" : "", use_l6 ? " l6" : "", use_wmax ? " wmax" : "", nspec, maxT);
    build_tables();
    if (noprune || getbit(F[b][0][0], 0)) dfs(0, 0, 0, 0);
    printf("DONE sunD2 b=%d N=%d part=%d/%d mode=%s%s%s%s%s spectra=%d nodes=%lld leaves=%lld tested=%lld cands=%lld\n",
           b, N, part, nparts, canon ? "canon" : "all", dry ? " dry" : "", use_l6 ? " l6" : "", use_wmax ? " wmax" : "", noprune ? " np" : "",
           nspec, nodes, leaves, tested, cands);
    return 0;
}
