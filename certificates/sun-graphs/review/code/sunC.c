/*
 * sunC.c -- referee's independent implementation C (written from scratch, 2026-09-26).
 *
 * Graph: cycle v_0..v_{b-1}; at v_k hang p_k pendant vertices (P1) and q_k pendant P2's
 * (strong reading: both kinds may sit at one vertex).  n = b + sum(p_k + 2 q_k).
 *
 * ENUMERATION (different from A and B): first the support pattern s_k in {0,1,2,3}
 * (bit0: p_k>0, bit1: q_k>0), one representative per dihedral orbit of patterns; then all
 * positive values on the support with n <= N.
 *
 * PRUNING (optional, flag 'prune'): rank-deficiency bound, derived independently in REVIEW.md:
 *   for integral G, r := #{eigenvalues with |lambda|>=2} = n - m0 - m(+1) - m(-1), and
 *   m0 <= P - |Kp| + d0(Kp), m(+1)+m(-1) <= 2Q (Kq nonempty) or <= 4 (Kq empty),
 *   where d0(Kp) = #cyclically consecutive Kp-pairs at even distance (Kp nonempty),
 *   d0(empty) = 2 if 4|b else 0.  Hence r >= b + |Kp| - d0 - (Kq empty ? 4 : 0).
 *   Each value |m|>=2 has multiplicity <= 2 and sum lambda^2 <= 2n, so r <= rmax(N).
 *   With 'noprune' every pattern with nmin <= N is enumerated.
 *
 * LEAF TEST (different from A and B): characteristic polynomial phi_G by Schwenk's cycle-edge
 * formula  phi(G) = phi(G-e) - phi(G-u-v) - 2 phi(G-V(C)),  e = v_{b-1}v_0,
 * with the caterpillar phi's computed by the bridge recurrence  A' = R_k A - l_k B, B' = l_k A,
 * all modulo two primes.  Integer-root multiplicities m in [-10,10] modulo p are upper bounds on
 * the true ones; if their sum is < n under either prime, G is certified NOT integral.
 * Survivors are printed and confirmed exactly (sympy) by confirmC.py.
 *
 * usage: sunC b N prune|noprune [allow3=1] [part nparts]
 *        sunC poly b p0 q0 ... : print phi mod P1 (validation mode)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef unsigned long long u64;
typedef unsigned __int128 u128;
#define MAXD 72
static const u64 PR[2] = {2305843009213693951ULL /* 2^61-1 */, 1000000000000000003ULL};

static int B, N, PRUNE, ALLOW3 = 1, PART = 0, NPARTS = 1;
static int RMAX;

static inline u64 mulm(u64 a, u64 b, u64 p) { return (u64)((u128)a * b % p); }
static inline u64 addm(u64 a, u64 b, u64 p) { u64 s = a + b; return s >= p ? s - p : s; }
static inline u64 subm(u64 a, u64 b, u64 p) { return a >= b ? a - b : a + p - b; }

typedef struct { int d; u64 c[MAXD]; } poly;

/* cache of leg polynomials for (p,q) with p+2q <= 60 */
#define WMAX 61
static poly Lc[2][WMAX][WMAX / 2 + 2], Rc[2][WMAX][WMAX / 2 + 2];

static void pmul(const poly *a, const poly *b, poly *r, u64 p) {
    poly t; t.d = a->d + b->d; memset(t.c, 0, sizeof(u64) * (t.d + 1));
    for (int i = 0; i <= a->d; i++) { if (!a->c[i]) continue;
        for (int j = 0; j <= b->d; j++) t.c[i + j] = addm(t.c[i + j], mulm(a->c[i], b->c[j], p), p); }
    *r = t;
}
static void psub(const poly *a, const poly *b, poly *r, u64 p) { /* r = a - b */
    poly t; t.d = a->d > b->d ? a->d : b->d;
    for (int i = 0; i <= t.d; i++) { u64 x = i <= a->d ? a->c[i] : 0, y = i <= b->d ? b->c[i] : 0; t.c[i] = subm(x, y, p); }
    while (t.d > 0 && t.c[t.d] == 0) t.d--;
    *r = t;
}
static void build_cache(void) {
    for (int ip = 0; ip < 2; ip++) { u64 p = PR[ip];
        for (int pp = 0; pp < WMAX; pp++) for (int qq = 0; pp + 2 * qq < WMAX; qq++) {
            /* l = x^pp (x^2-1)^qq */
            poly l; l.d = 0; l.c[0] = 1;
            poly xm1; xm1.d = 2; xm1.c[0] = p - 1; xm1.c[1] = 0; xm1.c[2] = 1;
            for (int t = 0; t < qq; t++) pmul(&l, &xm1, &l, p);
            poly sh; sh.d = l.d + pp; memset(sh.c, 0, sizeof(u64) * (sh.d + 1));
            for (int i = 0; i <= l.d; i++) sh.c[i + pp] = l.c[i];
            Lc[ip][pp][qq] = sh;
            /* s = pp x^{pp-1}(x^2-1)^qq + qq x^{pp+1}(x^2-1)^{qq-1} ; R = x*l - s */
            poly R; R.d = sh.d + 1; memset(R.c, 0, sizeof(u64) * (R.d + 1));
            for (int i = 0; i <= sh.d; i++) R.c[i + 1] = sh.c[i];
            if (pp > 0) { /* subtract pp * x^{pp-1} (x^2-1)^qq  = pp * l(x)/x */
                for (int i = 0; i <= l.d; i++) R.c[i + pp - 1] = subm(R.c[i + pp - 1], mulm(l.c[i], (u64)pp % p, p), p);
            }
            if (qq > 0) { poly l2; l2.d = 0; l2.c[0] = 1;
                for (int t = 0; t < qq - 1; t++) pmul(&l2, &xm1, &l2, p);
                for (int i = 0; i <= l2.d; i++) R.c[i + pp + 1] = subm(R.c[i + pp + 1], mulm(l2.c[i], (u64)qq % p, p), p);
            }
            while (R.d > 0 && R.c[R.d] == 0) R.d--;
            Rc[ip][pp][qq] = R;
        }
    }
}

static int PV[64], QV[64];

static void charpoly(int ip, poly *out) {
    u64 p = PR[ip];
    /* caterpillar on 0..b-1 */
    poly A = Rc[ip][PV[0]][QV[0]], Bp = Lc[ip][PV[0]][QV[0]], t1, t2;
    for (int k = 1; k < B; k++) {
        const poly *R = &Rc[ip][PV[k]][QV[k]], *L = &Lc[ip][PV[k]][QV[k]];
        pmul(R, &A, &t1, p); pmul(L, &Bp, &t2, p); poly nb; pmul(L, &A, &nb, p);
        psub(&t1, &t2, &A, p); Bp = nb;
    }
    /* caterpillar on 1..b-2 */
    poly A2 = Rc[ip][PV[1]][QV[1]], B2 = Lc[ip][PV[1]][QV[1]];
    for (int k = 2; k <= B - 2; k++) {
        const poly *R = &Rc[ip][PV[k]][QV[k]], *L = &Lc[ip][PV[k]][QV[k]];
        pmul(R, &A2, &t1, p); pmul(L, &B2, &t2, p); poly nb; pmul(L, &A2, &nb, p);
        psub(&t1, &t2, &A2, p); B2 = nb;
    }
    poly m1; pmul(&Lc[ip][PV[0]][QV[0]], &Lc[ip][PV[B - 1]][QV[B - 1]], &m1, p); pmul(&m1, &A2, &m1, p);
    poly all; all.d = 0; all.c[0] = 1;
    for (int k = 0; k < B; k++) pmul(&all, &Lc[ip][PV[k]][QV[k]], &all, p);
    for (int i = 0; i <= all.d; i++) all.c[i] = mulm(all.c[i], 2, p);
    poly r; psub(&A, &m1, &r, p); psub(&r, &all, &r, p);
    *out = r;
}

/* sum over m in [-10,10] of multiplicity of root m of f mod p */
static int rootsum(const poly *f0, u64 p, int *mult) {
    poly f = *f0; int tot = 0;
    for (int m = -10; m <= 10; m++) {
        u64 mm = m >= 0 ? (u64)m : p - (u64)(-m);
        int e = 0;
        while (f.d >= 1) {
            /* synthetic division by (x - mm) */
            u64 q[MAXD]; u64 acc = f.c[f.d];
            q[f.d - 1] = acc;
            for (int i = f.d - 1; i >= 1; i--) { acc = addm(f.c[i], mulm(acc, mm, p), p); q[i - 1] = acc; }
            u64 rem = addm(f.c[0], mulm(acc, mm, p), p);
            if (rem != 0) break;
            f.d -= 1; for (int i = 0; i <= f.d; i++) f.c[i] = q[i];
            e++;
        }
        if (mult) mult[m + 10] = e;
        tot += e;
    }
    return tot;
}

static long long leaves = 0, cand = 0, patterns_total = 0, patterns_kept = 0;

static int DRY = 0;
static void leaf(void) {
    int n = B; for (int k = 0; k < B; k++) n += PV[k] + 2 * QV[k];
    leaves++;
    if (DRY) return;
    poly f; charpoly(0, &f);
    if (f.d != n || f.c[n] != 1) { fprintf(stderr, "DEGREE ERROR n=%d d=%d\n", n, f.d); exit(3); }
    if (rootsum(&f, PR[0], NULL) < n) return;
    charpoly(1, &f);
    int mult[21];
    if (rootsum(&f, PR[1], mult) < n) return;
    cand++;
    printf("CAND b=%d n=%d :", B, n);
    for (int k = 0; k < B; k++) printf(" (%d,%d)", PV[k], QV[k]);
    printf("  modp-spec:");
    for (int m = -10; m <= 10; m++) if (mult[m + 10]) printf(" %d^%d", m, mult[m + 10]);
    printf("\n"); fflush(stdout);
}

static int pos[64], npos; static int kind[64]; /* kind: 0 = p value, 1 = q value */
static void assign(int i, int budget) { /* budget = N - n_so_far */
    if (i == npos) { leaf(); return; }
    int k = pos[i];
    if (kind[i] == 0) { for (int v = 1; v <= budget; v++) { PV[k] = v; assign(i + 1, budget - v); } PV[k] = 0; }
    else { for (int v = 1; 2 * v <= budget; v++) { QV[k] = v; assign(i + 1, budget - 2 * v); } QV[k] = 0; }
}

static int is_canonical(const int *s) {
    for (int r = 0; r < B; r++) for (int refl = 0; refl < 2; refl++) {
        if (r == 0 && refl == 0) continue;
        for (int k = 0; k < B; k++) {
            int j = refl ? ((r - k) % B + B) % B : (k + r) % B;
            if (s[j] < s[k]) return 0;   /* image is lexicographically smaller */
            if (s[j] > s[k]) break;
        }
    }
    return 1;
}

static int delta0(const int *s) {
    int kp[64], nk = 0;
    for (int k = 0; k < B; k++) if (s[k] & 1) kp[nk++] = k;
    if (nk == 0) return (B % 4 == 0) ? 2 : 0;
    int d = 0;
    for (int i = 0; i < nk; i++) { int g = (i + 1 < nk) ? kp[i + 1] - kp[i] : kp[0] + B - kp[i]; if (g % 2 == 0) d++; }
    return d;
}

int main(int argc, char **argv) {
    if (argc >= 2 && strcmp(argv[1], "poly") == 0) {
        B = atoi(argv[2]); for (int k = 0; k < B; k++) { PV[k] = atoi(argv[3 + 2 * k]); QV[k] = atoi(argv[4 + 2 * k]); }
        build_cache(); poly f; charpoly(0, &f);
        for (int i = 0; i <= f.d; i++) printf("%llu ", f.c[i]); printf("\n");
        int mult[21]; int t = rootsum(&f, PR[0], mult); printf("rootsum %d\n", t); return 0;
    }
    if (argc < 4) { fprintf(stderr, "usage\n"); return 1; }
    B = atoi(argv[1]); N = atoi(argv[2]); PRUNE = strcmp(argv[3], "prune") == 0;
    if (argc >= 5) ALLOW3 = atoi(argv[4]);
    if (argc >= 7) { PART = atoi(argv[5]); NPARTS = atoi(argv[6]); }
    /* rmax: largest r such that the r smallest admissible squares (4,4,4,4,9,9,9,9,16,...) sum <= 2N */
    { int s = 0, r = 0; for (int v = 2; ; v++) { int stop = 0; for (int t = 0; t < 4; t++) { if (s + v * v > 2 * N) { stop = 1; break; } s += v * v; r++; } if (stop) break; } RMAX = r; }
    if (getenv("SUNC_DRY")) DRY = 1;
    build_cache();
    int s[64]; long long code, ncode = 1LL << (2 * B);
    for (code = 1; code < ncode; code++) {
        if (NPARTS > 1 && (code % NPARTS) != PART) continue;
        int np = 0, nq = 0, bad = 0;
        for (int k = 0; k < B; k++) { s[k] = (code >> (2 * k)) & 3; if (s[k] == 3 && !ALLOW3) bad = 1; np += s[k] & 1; nq += (s[k] >> 1) & 1; }
        if (bad) continue;
        if (B + np + 2 * nq > N) continue;
        if (!is_canonical(s)) continue;
        patterns_total++;
        if (PRUNE) {
            int rlb = B + np - delta0(s) - (nq == 0 ? 4 : 0);
            if (rlb > RMAX) continue;
        }
        patterns_kept++;
        npos = 0;
        for (int k = 0; k < B; k++) { if (s[k] & 1) { pos[npos] = k; kind[npos++] = 0; } if (s[k] & 2) { pos[npos] = k; kind[npos++] = 1; } }
        for (int k = 0; k < B; k++) { PV[k] = 0; QV[k] = 0; }
        assign(0, N - B);
    }
    printf("C-DONE b=%d N=%d prune=%d allow3=%d part=%d/%d rmax=%d patterns=%lld kept=%lld leaves=%lld candidates=%lld\n",
           B, N, PRUNE, ALLOW3, PART, NPARTS, RMAX, patterns_total, patterns_kept, leaves, cand);
    return 0;
}
