/*
 * sunsearch.c  (implementation A)
 * Exhaustive search for integral generalized sun graphs G = cycle C_b with, at each
 * cycle vertex k, p_k pendant vertices (copies of P_1) and q_k pendant P_2's
 * (strong reading: both kinds may sit at the same vertex).  Order n = b + sum(p_k+2q_k).
 * Longer pendant paths are excluded by Theorem 2.1 of arXiv:2609.28754.
 *
 * Usage: sunsearch b NMAX [part nparts]      -> DFS search, prints integral graphs found
 *        sunsearch test                     -> reads "b p_0 q_0 ... p_{b-1} q_{b-1}" lines,
 *                                              prints n and exact multiplicities (for validation)
 *
 * Soundness of pruning: see PROOF.md (Lemmas 1-7).  Leaves are decided EXACTLY:
 *   mult(0), mult(+1), mult(-1) by exact integer formulas (Lemma 3),
 *   mult(m), 2<=|m|<=9, by the monodromy matrix of the cycle recurrence (Lemma 2), computed
 *   modulo four 62-bit primes with a magnitude bound that makes congruence equivalent to equality.
 *   G integral  <=>  sum_m mult(m) = n.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

typedef __int128 i128;
typedef unsigned __int128 u128;
typedef long long ll;

static int B, NMAX, MMAX = 9, PART = 0, NPARTS = 1;
static const uint64_t PR[4] = {4611686018427387847ULL, 4611686018427387817ULL,
                               4611686018427387787ULL, 4611686018427387761ULL};

/* ------------------------------------------------------------------ */
/* admissible spectra (Lemma 5)                                        */
typedef struct { int gt[10]; int ge[10]; ll m4; ll s2; } Feat;
static Feat *feats = NULL; static int nfeats = 0, capf = 0;
/* all admissible (m4, s2) pairs, for the exact moment identities at leaves (Lemma 5) */
static ll *allm4 = NULL, *alls2 = NULL; static int nall = 0;
static int dominated(const Feat *x, const Feat *y) { /* y >= x componentwise */
    for (int m = 1; m <= 9; m++) if (y->gt[m] < x->gt[m] || y->ge[m] < x->ge[m]) return 0;
    return y->m4 >= x->m4 && y->s2 >= x->s2;
}
static void addfeat(Feat f) {
    if (nfeats == capf) { capf = capf ? 2 * capf : 1024; feats = realloc(feats, capf * sizeof(Feat)); }
    feats[nfeats++] = f;
}
static ll ipow(ll v, int e) { ll r = 1; while (e--) r *= v; return r; }

static void gen_spectra(void) {
    int even = (B % 2 == 0);
    int cp[10], cm[10];
    long total = 0;
    /* enumerate multiplicity vectors cp[v], v=2..9, in {0,1,2} */
    for (int code = 0; code < 6561; code++) {
        int t = code; for (int v = 2; v <= 9; v++) { cp[v] = t % 3; t /= 3; }
        int rho = 0; for (int v = 9; v >= 2; v--) if (cp[v]) { rho = v; break; }
        if (rho < 3 || cp[rho] != 1) continue;           /* Perron root simple, rho >= 3 */
        ll s2p = 0; for (int v = 2; v <= 9; v++) s2p += (ll)cp[v] * v * v;
        if (even) {
            if (s2p > NMAX) continue;                     /* sum_{lambda>0} lambda^2 = n <= NMAX */
            Feat f; memset(&f, 0, sizeof f);
            for (int m = 1; m <= 9; m++) { int g = 0, e = 0; for (int v = 2; v <= 9; v++) { if (v > m) g += cp[v]; if (v >= m) e += cp[v]; } f.gt[m] = g; f.ge[m] = (m >= 2) ? e : 0; }
            for (int v = 2; v <= 9; v++) f.m4 += (ll)cp[v] * v * v * (v * v - 1);
            f.s2 = s2p; addfeat(f); total++;
        } else {
            for (int code2 = 0; code2 < 6561; code2++) {
                int t2 = code2, ok = 1; for (int v = 2; v <= 9; v++) { cm[v] = t2 % 3; t2 /= 3; if (cm[v] && v >= rho) ok = 0; }
                if (!ok) continue;                        /* -rho is not an eigenvalue (non-bipartite) */
                ll s2 = s2p; for (int v = 2; v <= 9; v++) s2 += (ll)cm[v] * v * v;
                if (s2 > 2LL * NMAX) continue;            /* sum lambda^2 <= 2n */
                /* odd moments: sum_{|l|>=2} (l^L - l) = 0 for odd 3<=L<B, = 2B for L=B */
                for (int L = 3; L <= B && ok; L += 2) {
                    ll S = 0; for (int v = 2; v <= 9; v++) S += (ll)(cp[v] - cm[v]) * (ipow(v, L) - v);
                    if (L < B && S != 0) ok = 0;
                    if (L == B && S != 2LL * B) ok = 0;
                }
                if (!ok) continue;
                Feat f; memset(&f, 0, sizeof f);
                for (int m = 1; m <= 9; m++) {
                    int gp = 0, ep = 0, gm = 0, em = 0;
                    for (int v = 2; v <= 9; v++) { if (v > m) { gp += cp[v]; gm += cm[v]; } if (v >= m) { ep += cp[v]; em += cm[v]; } }
                    f.gt[m] = gp < gm ? gp : gm; f.ge[m] = (m >= 2) ? (ep < em ? ep : em) : 0;
                }
                for (int v = 2; v <= 9; v++) f.m4 += (ll)(cp[v] + cm[v]) * v * v * (v * v - 1);
                f.s2 = s2; addfeat(f); total++;
            }
        }
    }
    allm4 = malloc((nfeats + 1) * sizeof(ll)); alls2 = malloc((nfeats + 1) * sizeof(ll)); nall = nfeats;
    for (int i = 0; i < nfeats; i++) { allm4[i] = feats[i].m4; alls2[i] = feats[i].s2; }
    /* Pareto reduction */
    int keep = 0;
    for (int i = 0; i < nfeats; i++) {
        int dom = 0;
        for (int j = 0; j < nfeats && !dom; j++) {
            if (j == i) continue;
            if (dominated(&feats[i], &feats[j])) {
                if (!dominated(&feats[j], &feats[i]) || j < i) dom = 1; /* strictly dominated, or duplicate kept once */
            }
        }
        if (!dom) feats[keep++] = feats[i];
    }
    fprintf(stderr, "b=%d NMAX=%d admissible spectra=%ld pareto=%d\n", B, NMAX, total, keep);
    nfeats = keep;
}

/* ------------------------------------------------------------------ */
/* exact tridiagonal inertia on paths (Lemma 4)                        */
typedef struct { int st; i128 a, c; } Piv;          /* st: 0 START, 1 ZERO, 2 FINITE (a/c, c>0) */
typedef struct { Piv p; int cnt; int len; } Seq;
static i128 gcd128(i128 x, i128 y) { if (x < 0) x = -x; if (y < 0) y = -y; while (y) { i128 t = x % y; x = y; y = t; } return x; }
static long overflow_skips = 0;
/* append a vertex with diagonal entry sigma = s/D (D>0), off-diagonal 1.
   plus=1: count positive pivots (n_+ with the "-0 then +inf" zero rule);
   plus=0: count negative pivots (n_- with the "+0 then -inf" zero rule). */
static inline void upd(Seq *out, const Seq *in, i128 s, i128 D, int plus) {
    *out = *in;
    if (in->p.st == 1) { out->cnt++; out->p.st = 0; out->len++; return; }
    i128 num, den;
    if (in->p.st == 0) { num = s; den = D; }
    else {
        i128 t1, t2;
        if (__builtin_mul_overflow(s, in->p.a, &t1) || __builtin_mul_overflow(D, in->p.c, &t2) ||
            __builtin_sub_overflow(t1, t2, &num) || __builtin_mul_overflow(D, in->p.a, &den)) {
            overflow_skips++; out->p.st = 0; return;   /* drop this vertex: principal submatrix */
        }
        if (den < 0) { num = -num; den = -den; }
    }
    if (num == 0) { out->p.st = 1; out->len++; return; }
    i128 g = gcd128(num, den); num /= g; den /= g;
    out->p.st = 2; out->p.a = num; out->p.c = den; out->len++;
    if (plus) { if (num > 0) out->cnt++; } else { if (num < 0) out->cnt++; }
}

/* ------------------------------------------------------------------ */
/* exact leaf test                                                     */
static int P_[64], Q_[64];
static uint64_t mulmod(uint64_t a, uint64_t b, uint64_t p) { return (uint64_t)((u128)a * b % p); }
static uint64_t modred(i128 x, uint64_t p) { i128 r = x % (i128)p; if (r < 0) r += p; return (uint64_t)r; }
static int mult_m(int m) {           /* multiplicity of integer m, |m|>=2 */
    i128 D = (i128)m * (m * m - 1);
    double lg = 0; for (int k = 0; k < B; k++) {
        i128 s = (i128)m * m * (m * m - 1) - (i128)P_[k] * (m * m - 1) - (i128)Q_[k] * m * m;
        double as = (double)(s < 0 ? -s : s) + fabs((double)D); lg += log2(as);
    }
    double lgD = B * log2(fabs((double)D));
    double lgb = (lg > lgD ? lg : lgD) + 3.0;   /* |tr P - 2D^b| <= 2*prod + 2|D|^b <= 2^(max+2) */
    if (lgb > 240.0) { fprintf(stderr, "magnitude bound too large\n"); exit(3); }
    int trok = 1, scal = 1;
    for (int ip = 0; ip < 4; ip++) {
        uint64_t p = PR[ip];
        uint64_t M00 = 1, M01 = 0, M10 = 0, M11 = 1;
        uint64_t d = modred(D, p), md = modred(-D, p);
        for (int k = 0; k < B; k++) {
            i128 s = (i128)m * m * (m * m - 1) - (i128)P_[k] * (m * m - 1) - (i128)Q_[k] * m * m;
            uint64_t sm = modred(s, p);
            /* T = [[s, -D],[D, 0]] ; M <- T*M */
            uint64_t n00 = (mulmod(sm, M00, p) + mulmod(md, M10, p)) % p;
            uint64_t n01 = (mulmod(sm, M01, p) + mulmod(md, M11, p)) % p;
            uint64_t n10 = mulmod(d, M00, p);
            uint64_t n11 = mulmod(d, M01, p);
            M00 = n00; M01 = n01; M10 = n10; M11 = n11;
        }
        uint64_t Db = 1; for (int k = 0; k < B; k++) Db = mulmod(Db, d, p);
        if ((M00 + M11) % p != (2 * (u128)Db) % p) trok = 0;
        if (!(M00 == Db && M11 == Db && M01 == 0 && M10 == 0)) scal = 0;
    }
    if (scal) return 2;
    if (trok) return 1;
    return 0;
}
/* dimension of cycle solutions: zeros forced on set Z (zmask[k]=1), recurrence
   x_{k-1}+x_{k+1} = c_k x_k at k not in Z.  Exact integers. */
static int cycdim(const int *zmask, const ll *c) {
    int any = 0; for (int k = 0; k < B; k++) any |= zmask[k];
    if (!any) {  /* monodromy of [[c,-1],[1,0]], exact i128 */
        i128 M00 = 1, M01 = 0, M10 = 0, M11 = 1;
        for (int k = 0; k < B; k++) {
            i128 n00 = c[k] * M00 - M10, n01 = c[k] * M01 - M11;
            M10 = M00; M11 = M01; M00 = n00; M01 = n01;
        }
        if (M00 == 1 && M11 == 1 && M01 == 0 && M10 == 0) return 2;
        if (M00 + M11 == 2) return 1;
        return 0;
    }
    int dim = 0;
    for (int k1 = 0; k1 < B; k1++) {
        if (!zmask[k1]) continue;
        int g = 1; while (!zmask[(k1 + g) % B]) g++;   /* next zero-forced vertex */
        if (g == 1) continue;
        i128 xprev = 0, x = 1;                        /* x_{k1}=0, x_{k1+1}=1 */
        for (int t = 1; t < g; t++) {                 /* recurrence at vertex k1+t */
            int v = (k1 + t) % B;
            i128 xn = (i128)c[v] * x - xprev; xprev = x; x = xn;
        }
        if (x == 0) dim++;                            /* x_{k2} = 0 automatically */
    }
    return dim;
}
static int total_mult(int *mm, int *nn) {
    int n = B; for (int k = 0; k < B; k++) n += P_[k] + 2 * Q_[k];
    int z[64]; ll c[64]; int tot = 0;
    /* eigenvalue 0 */
    int s0 = 0; for (int k = 0; k < B; k++) { z[k] = P_[k] > 0; c[k] = 0; if (P_[k] > 0) s0 += P_[k] - 1; }
    mm[9 + 0] = s0 + cycdim(z, c);
    /* eigenvalues +1 and -1 */
    int sq = 0; for (int k = 0; k < B; k++) { z[k] = Q_[k] > 0; if (Q_[k] > 0) sq += Q_[k] - 1; }
    for (int k = 0; k < B; k++) c[k] = 1 - P_[k];
    mm[9 + 1] = sq + cycdim(z, c);
    for (int k = 0; k < B; k++) c[k] = P_[k] - 1;
    mm[9 - 1] = sq + cycdim(z, c);
    for (int m = 2; m <= 9; m++) { mm[9 + m] = mult_m(m); mm[9 - m] = mult_m(-m); }
    for (int i = 0; i <= 18; i++) tot += mm[i];
    *nn = n; return tot;
}

/* ------------------------------------------------------------------ */
/* DFS                                                                 */
typedef struct { Seq R; Seq Sp[10], Sm[10]; int nq; ll W, P, Q, lb4; } State;
static State st[64];
static long nodes = 0, leaves = 0, found = 0, pruned = 0, momfail = 0;
static int leaf_moments(void) {
    ll sdd = 0, P = 0, Q = 0, n = B;
    for (int k = 0; k < B; k++) { ll d = 2 + P_[k] + Q_[k]; sdd += d * (d - 1) + 2LL * Q_[k]; P += P_[k]; Q += Q_[k]; n += P_[k] + 2 * Q_[k]; }
    ll target = (B % 2 == 0) ? sdd + (B == 4 ? 4 : 0) : 2 * sdd;     /* 4th moment identity */
    ll mq = Q > 2 ? Q : 2;
    ll lo = (B % 2 == 0) ? n - mq : 2 * n - 2 * mq, hi = (B % 2 == 0) ? n : 2 * n; /* 2nd moment */
    for (int i = 0; i < nall; i++) if (allm4[i] == target && alls2[i] >= lo && alls2[i] <= hi) return 1;
    return 0;
}
static int key(int p, int q) { return p * 1000 + q; }        /* total order on (p,q) */

static int feasible(const State *S, int depth) {
    int Lgt[10], Lge[10];
    Lgt[1] = S->nq + S->R.cnt; Lge[1] = 0;
    for (int m = 2; m <= 9; m++) { Lgt[m] = S->Sp[m].cnt; Lge[m] = S->Sm[m].len - S->Sm[m].cnt; }
    ll lb4 = S->lb4 + 2LL * (B - depth);
    ll c4 = (B % 2 == 0) ? 1 : 2;
    ll s2low = (B % 2 == 0) ? (B + S->P + S->Q - 2) : 2 * (B + S->P + S->Q - 2);
    for (int i = 0; i < nfeats; i++) {
        const Feat *f = &feats[i]; int ok = 1;
        if (f->m4 < c4 * lb4 || f->s2 < s2low) continue;
        for (int m = 1; m <= 9 && ok; m++) if (f->gt[m] < Lgt[m] || f->ge[m] < Lge[m]) ok = 0;
        if (ok) return 1;
    }
    return 0;
}

static void push(int depth, int p, int q) {     /* assign vertex depth-1 := (p,q), build st[depth] */
    State *o = &st[depth]; const State *in = &st[depth - 1];
    o->W = in->W + p + 2 * q; o->P = in->P + p; o->Q = in->Q + q;
    o->lb4 = in->lb4 + (ll)(2 + p + q) * (1 + p + q) + 2LL * q;
    if (q > 0) { o->R = in->R; o->R.p.st = 0; o->nq = in->nq + 1; }
    else { upd(&o->R, &in->R, (i128)(p - 1), 1, 1); o->nq = in->nq; }
    for (int m = 2; m <= MMAX; m++) {
        i128 D = (i128)m * (m * m - 1);
        i128 s = -(i128)m * D + (i128)p * (m * m - 1) + (i128)q * m * m;
        upd(&o->Sp[m], &in->Sp[m], s, D, 1);
        upd(&o->Sm[m], &in->Sm[m], s, D, 0);
    }
    for (int m = MMAX + 1; m <= 9; m++) { o->Sp[m] = in->Sp[m]; o->Sm[m] = in->Sm[m]; }
}

static void dfs(int depth, int k0) {           /* depth = number of assigned vertices */
    nodes++;
    if (depth == B) {
        if (st[depth].W == 0) return;           /* the bare cycle is not a counterexample */
        leaves++;
        if (!leaf_moments()) { momfail++; return; }
        int mm[19], n; int tot = total_mult(mm, &n);
        if (tot > n) { fprintf(stderr, "BUG: multiplicities exceed n\n"); exit(4); }
        if (tot == n) {
            found++;
            printf("INTEGRAL b=%d n=%d :", B, n);
            for (int k = 0; k < B; k++) printf(" (%d,%d)", P_[k], Q_[k]);
            printf("  spec:"); for (int i = 0; i <= 18; i++) if (mm[i]) printf(" %d^%d", i - 9, mm[i]);
            printf("\n"); fflush(stdout);
        }
        return;
    }
    ll rem = NMAX - B - st[depth].W;
    /* Lemma 6 (monotonicity): every pruning lower bound is non-decreasing in p_k and q_k, so once
       (p,q) is infeasible, so is every (p',q') with p'>=p, q'>=q.                                   */
    for (int q = 0; 2 * q <= rem; q++) {
        int p0feasible = 0;
        for (int p = 0; p + 2 * q <= rem; p++) {
            if (depth > 0 && key(p, q) > k0) break;   /* vertex 0 carries a maximal key; key increasing in p */
            P_[depth] = p; Q_[depth] = q;
            push(depth + 1, p, q);
            if (!feasible(&st[depth + 1], depth + 1)) { pruned++; break; }
            if (p == 0) p0feasible = 1;
            if (depth == 0 && (key(p, q) % NPARTS) != PART) continue;
            dfs(depth + 1, depth == 0 ? key(p, q) : k0);
        }
        if (!p0feasible) break;
    }
}

int main(int argc, char **argv) {
    if (argc >= 2 && strcmp(argv[1], "test") == 0) {
        int b; while (scanf("%d", &b) == 1) {
            B = b; for (int k = 0; k < B; k++) if (scanf("%d %d", &P_[k], &Q_[k]) != 2) return 1;
            int mm[19], n; int tot = total_mult(mm, &n);
            printf("%d %d", n, tot); for (int i = 0; i <= 18; i++) printf(" %d", mm[i]); printf("\n");
        }
        return 0;
    }
    if (argc < 3) { fprintf(stderr, "usage\n"); return 1; }
    B = atoi(argv[1]); NMAX = atoi(argv[2]);
    if (argc >= 5) { PART = atoi(argv[3]); NPARTS = atoi(argv[4]); }
    MMAX = (int)floor(sqrt(2.0 * NMAX)); if (MMAX > 9) MMAX = 9;
    if (2 * NMAX >= 100) { fprintf(stderr, "NMAX too large for value range 2..9\n"); return 1; }
    gen_spectra();
    memset(&st[0], 0, sizeof(State));
    st[0].R.p.st = 0; for (int m = 0; m < 10; m++) { st[0].Sp[m].p.st = 0; st[0].Sm[m].p.st = 0; }
    dfs(0, 0);
        printf("DONE b=%d NMAX=%d part=%d/%d nodes=%ld pruned=%ld leaves=%ld momentfail=%ld exacttested=%ld integral=%ld overflow_skips=%ld\n",
           B, NMAX, PART, NPARTS, nodes, pruned, leaves, momfail, leaves - momfail, found, overflow_skips);
    return 0;
}
