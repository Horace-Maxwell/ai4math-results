/*
 * sunB.c  (implementation B, written independently of sunsearch.c)
 * Different pruning: only the 2nd/4th moment identities (no inertia counts).
 * Different leaf test: F(x) = det( x(x^2-1)(xI - A(C_b)) - diag(p_k(x^2-1) + q_k x^2) ), monic of
 * degree 4b, is computed modulo primes by evaluation at 3b+1 points + Newton interpolation; the
 * multiplicities of the integers -9..9 as roots of F mod p are upper bounds for the true ones, so
 * sum < 4b certifies non-integrality.  Candidates with sum = 4b for all primes are printed for an
 * exact (sympy) confirmation.
 * Each graph is tested once: only dihedrally canonical sequences ((p_0,q_0),...,(p_{b-1},q_{b-1}))
 * (lexicographically least among the 2b rotations/reflections) are tested.
 * Usage: sunB2 b NMAX [part nparts]
 * sunB2 = sunB plus a floating-point interlacing prune (LAPACK dsyev on the weighted reduced matrix
 * of the partial caterpillar on cycle vertices 0..k-1, k <= b-1, an induced subgraph of G):
 * a node is pruned only if, for every admissible spectrum, some count #{eig > m + 1e-6} exceeds
 * #{B+ > m}.  (Cross-check only; the rigorous search is implementation A.)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
typedef long long ll;
extern void dsyev_(char *jobz, char *uplo, int *n, double *a, int *lda, double *w, double *work, int *lwork, int *info);
static int PART = 0, NPARTS = 1;
static int specC[100000][10];   /* specC[i][m] = #{lambda in B+ : lambda > m}, m = 1..9 */
typedef unsigned __int128 u128;

static int b, NMAX;
static int pp[64], qq[64];
static const uint64_t PRIMES[3] = {1000000007ULL, 998244353ULL, 2305843009213693951ULL};

/* spectra: T4 = sum_{|l|>=2} l^2(l^2-1) (over B+ for even b; over B+ and B- for odd b), S2 = sum l^2 */
static ll specT[100000], specS[100000]; static int nspec = 0;
static int cpos[10], cneg[10];
static ll powll(ll v, int e) { ll r = 1; for (int i = 0; i < e; i++) r *= v; return r; }
static int cycGT1 = -1;   /* number of eigenvalues 2cos(2 pi j/b) of C_b that exceed 1 */
static void record(void) {
    ll T = 0, S = 0;
    if (cycGT1 < 0) { cycGT1 = 0; for (int j = 0; j < b; j++) if (j * 6 < b || (b - j) * 6 < b) cycGT1++; }
    { int npos = 0; for (int v = 2; v <= 9; v++) npos += cpos[v]; if (npos < cycGT1) return; }  /* interlacing with induced C_b */
    for (int v = 2; v <= 9; v++) { T += (ll)(cpos[v] + cneg[v]) * v * v * (v * v - 1); S += (ll)(cpos[v] + cneg[v]) * v * v; }
    if (b % 2 == 0) { if (S > NMAX) return; }
    else {
        if (S > 2LL * NMAX) return;
        for (int L = 3; L <= b; L += 2) {          /* closed odd walks: tr A^L = 0 (L<b), 2b (L=b) */
            ll s = 0; for (int v = 2; v <= 9; v++) s += (ll)(cpos[v] - cneg[v]) * (powll(v, L) - v);
            if (s != (L == b ? 2LL * b : 0)) return;
        }
    }
    for (int m = 1; m <= 9; m++) { int c = 0; for (int v = 2; v <= 9; v++) if (v > m) c += cpos[v]; specC[nspec][m] = c; }
    specT[nspec] = T; specS[nspec] = S; nspec++;
}
static void recneg(int v, int rho) {                 /* B- values -v, v < rho, multiplicity <= 2 */
    if (v >= rho || v > 9) { record(); return; }
    for (int c = 0; c <= 2; c++) { cneg[v] = c; recneg(v + 1, rho); }
    cneg[v] = 0;
}
static void recpos(int v) {                          /* B+ values v = 2..9, multiplicity <= 2 */
    if (v > 9) {
        int rho = 0; for (int w = 9; w >= 2; w--) if (cpos[w]) { rho = w; break; }
        if (rho < 3 || cpos[rho] != 1) return;
        if (b % 2 == 0) { memset(cneg, 0, sizeof cneg); record(); }   /* bipartite: sums over B+ only */
        else recneg(2, rho);
        return;
    }
    for (int c = 0; c <= 2; c++) { cpos[v] = c; recpos(v + 1); }
    cpos[v] = 0;
}

/* modular arithmetic */
static uint64_t mm(uint64_t a, uint64_t c, uint64_t p) { return (uint64_t)((u128)a * c % p); }
static uint64_t pw(uint64_t a, uint64_t e, uint64_t p) { uint64_t r = 1; a %= p; while (e) { if (e & 1) r = mm(r, a, p); a = mm(a, a, p); e >>= 1; } return r; }
static uint64_t md(ll x, uint64_t p) { __int128 y = (__int128)x % (__int128)p; if (y < 0) y += p; return (uint64_t)y; }
static uint64_t detmod(uint64_t M[64][64], int n, uint64_t p) {
    uint64_t det = 1;
    for (int c = 0; c < n; c++) {
        int piv = -1; for (int r = c; r < n; r++) if (M[r][c]) { piv = r; break; }
        if (piv < 0) return 0;
        if (piv != c) { for (int k = 0; k < n; k++) { uint64_t t = M[c][k]; M[c][k] = M[piv][k]; M[piv][k] = t; } det = (p - det) % p; }
        det = mm(det, M[c][c], p);
        uint64_t inv = pw(M[c][c], p - 2, p);
        for (int r = c + 1; r < n; r++) if (M[r][c]) {
            uint64_t f = mm(M[r][c], inv, p);
            for (int k = c; k < n; k++) M[r][k] = (M[r][k] + p - mm(f, M[c][k], p)) % p;
        }
    }
    return det;
}
/* sum over m in [-9,9] of the multiplicity of m as a root of F mod p */
static int rootsum_mod(uint64_t p) {
    int N = 4 * b;                                   /* deg F = 4b (F = (x(x^2-1))^b det(xI-C-diag f)) */
    static uint64_t xs[200], ys[200], coef[200];
    for (int i = 0; i <= N; i++) {
        uint64_t x = (uint64_t)(i + 20) % p;         /* evaluation points 20..20+3b */
        uint64_t x2 = mm(x, x, p), x2m1 = (x2 + p - 1) % p, off = (p - mm(x, x2m1, p)) % p;
        static uint64_t M[64][64];
        for (int r = 0; r < b; r++) for (int c = 0; c < b; c++) M[r][c] = 0;
        for (int r = 0; r < b; r++) {
            /* diagonal: x^2(x^2-1) - p_r(x^2-1) - q_r x^2 */
            uint64_t d = (mm(x2, x2m1, p) + p - mm((uint64_t)pp[r] % p, x2m1, p)) % p;
            d = (d + p - mm((uint64_t)qq[r] % p, x2, p)) % p;
            M[r][r] = d;
            M[r][(r + 1) % b] = off; M[r][(r + b - 1) % b] = off;
        }
        xs[i] = x; ys[i] = detmod(M, b, p);
    }
    /* Newton divided differences -> monomial coefficients */
    static uint64_t dd[200];
    for (int i = 0; i <= N; i++) dd[i] = ys[i];
    for (int j = 1; j <= N; j++) for (int i = N; i >= j; i--) {
        uint64_t num = (dd[i] + p - dd[i - 1]) % p, den = (xs[i] + p - xs[i - j]) % p;
        dd[i] = mm(num, pw(den, p - 2, p), p);
    }
    for (int i = 0; i <= N; i++) coef[i] = 0;
    coef[0] = dd[N];
    int deg = 0;
    for (int j = N - 1; j >= 0; j--) {               /* coef <- coef*(x - xs[j]) + dd[j] */
        for (int k = deg + 1; k >= 1; k--) coef[k] = (coef[k - 1] + p - mm(coef[k], xs[j], p)) % p;
        coef[0] = (p - mm(coef[0], xs[j], p)) % p;
        deg++;
        coef[0] = (coef[0] + dd[j]) % p;
    }
    if (coef[N] != 1) { fprintf(stderr, "B: F not monic mod p?\n"); exit(5); }
    int tot = 0;
    for (int m = -9; m <= 9; m++) {
        static uint64_t w[200]; int dg = N; for (int k = 0; k <= N; k++) w[k] = coef[k];
        uint64_t r = md(m, p);
        while (dg > 0) {                              /* synthetic division by (x - r) */
            static uint64_t qv[200]; uint64_t acc = 0;
            for (int k = dg; k >= 0; k--) { acc = (mm(acc, r, p) + w[k]) % p; if (k > 0) qv[k - 1] = acc; }
            if (acc != 0) break;
            for (int k = 0; k < dg; k++) w[k] = qv[k];
            dg--; tot++;
        }
    }
    return tot;
}
static int canonical(void) {
    for (int s = 0; s < b; s++) for (int dir = -1; dir <= 1; dir += 2) {
        if (s == 0 && dir == 1) continue;
        for (int k = 0; k < b; k++) {
            int j = ((dir == 1 ? s + k : s - k) % b + b) % b;
            int a0 = pp[k] * 1000 + qq[k], a1 = pp[j] * 1000 + qq[j];
            if (a1 > a0) return 0;            /* B2: canonical = lexicographically GREATEST image */
            if (a1 < a0) break;
        }
    }
    return 1;
}
static ll maxT = 0; static long tested = 0, canon = 0, found = 0, momok = 0;
static void leaf(void) {
    ll P = 0, Q = 0, M = 0; int n = b;
    for (int k = 0; k < b; k++) { ll d = 2 + pp[k] + qq[k]; M += d * (d - 1) + 2LL * qq[k]; P += pp[k]; Q += qq[k]; n += pp[k] + 2 * qq[k]; }
    if (P + Q == 0) return;
    ll T = (b % 2 == 0) ? M + (b == 4 ? 4 : 0) : 2 * M, mq = Q > 2 ? Q : 2;   /* b=4: tr A^4 has +8 */
    ll lo = (b % 2 == 0) ? n - mq : 2 * n - 2 * mq, hi = (b % 2 == 0) ? n : 2 * n;
    int ok = 0; for (int i = 0; i < nspec && !ok; i++) if (specT[i] == T && specS[i] >= lo && specS[i] <= hi) ok = 1;
    if (!ok) return;
    momok++;
    printf("LEAF"); for (int k = 0; k < b; k++) printf(" %d,%d", pp[k], qq[k]); printf("\n");
    if (!canonical()) return;
    canon++;
    for (int ip = 0; ip < 3; ip++) if (rootsum_mod(PRIMES[ip]) < 4 * b) { tested++; return; }
    tested++; found++;
    printf("CANDIDATE b=%d n=%d :", b, n); for (int k = 0; k < b; k++) printf(" (%d,%d)", pp[k], qq[k]); printf("\n"); fflush(stdout);
}
static long lapack_pruned = 0;
static int interlace_ok(int k) {          /* vertices 0..k-1 assigned, k <= b-1 */
    /* Induced subgraph H of G: cycle vertices 0..b-2 (a path; the edge (b-1,0) is absent because
       vertex b-1 is omitted) together with the attachments of the assigned vertices 0..k-1 only.
       Every such H is an induced subgraph of every completion G, so N_{>m}(G) >= N_{>m}(H).     */
    int n = 0, L = b - 1; double A[128 * 128];
    int pos[64], pend[64], u2[64];
    for (int v = 0; v < L; v++) { pos[v] = n++; }
    for (int v = 0; v < k; v++) { pend[v] = pp[v] > 0 ? n++ : -1; if (qq[v] > 0) { u2[v] = n; n += 2; } else u2[v] = -1; }
    for (int i = 0; i < n * n; i++) A[i] = 0;
    for (int v = 0; v + 1 < L; v++) { A[pos[v] * n + pos[v + 1]] = A[pos[v + 1] * n + pos[v]] = 1; }
    for (int v = 0; v < k; v++) {
        if (pend[v] >= 0) { double w = sqrt((double)pp[v]); A[pos[v] * n + pend[v]] = A[pend[v] * n + pos[v]] = w; }
        if (u2[v] >= 0) { double w = sqrt((double)qq[v]); A[pos[v] * n + u2[v]] = A[u2[v] * n + pos[v]] = w; A[u2[v] * n + u2[v] + 1] = A[(u2[v] + 1) * n + u2[v]] = 1; }
    }
    double ev[128], work[128 * 8]; int lwork = 128 * 8, info; char jobz = 'N', uplo = 'U';
    dsyev_(&jobz, &uplo, &n, A, &n, ev, work, &lwork, &info);
    if (info != 0) return 1;                  /* no pruning on failure */
    int cnt[10]; for (int m = 1; m <= 9; m++) { cnt[m] = 0; for (int i = 0; i < n; i++) if (ev[i] > m + 1e-6) cnt[m]++; }
    for (int i = 0; i < nspec; i++) { int ok = 1; for (int m = 1; m <= 9 && ok; m++) if (cnt[m] > specC[i][m]) ok = 0; if (ok) return 1; }
    lapack_pruned++;
    return 0;
}
static void dfs(int k, int W, ll M) {
    int rem = NMAX - b - W;
    if (k == b) { leaf(); return; }
    /* (interlacing prune is applied to children inside the loop, with monotone breaks) */
    ll lastT = (b % 2 == 0) ? maxT - (b == 4 ? 4 : 0) : maxT / 2;
    for (int q = 0; 2 * q <= rem; q++) { int p0ok = 0; for (int p = 0; p + 2 * q <= rem; p++) {
        ll d = 2 + p + q; ll M2 = M + d * (d - 1) + 2LL * q;
        if (M2 + 2LL * (b - k - 1) > lastT) break;   /* increasing in p */
        if (k == 0 && ((p * 1000 + q) % NPARTS) != PART) { if (p == 0) p0ok = 1; continue; }
        if (k >= 1 && p * 1000 + q > pp[0] * 1000 + qq[0]) break;   /* greatest image starts with a max key */
        pp[k] = p; qq[k] = q;
        /* child = vertices 0..k assigned; prune by interlacing if k+1 <= b-1 (monotone in p and q) */
        if (b % 2 == 0 && k + 1 <= b - 1 && !interlace_ok(k + 1)) break;
        if (p == 0) p0ok = 1;
        dfs(k + 1, W + p + 2 * q, M2);
    } if (!p0ok) break; }
}
int main(int argc, char **argv) {
    b = atoi(argv[1]); NMAX = atoi(argv[2]); if (argc >= 5) { PART = atoi(argv[3]); NPARTS = atoi(argv[4]); }
    recpos(2);
    for (int i = 0; i < nspec; i++) if (specT[i] > maxT) maxT = specT[i];
    fprintf(stderr, "B: b=%d NMAX=%d spectra=%d maxT=%lld\n", b, NMAX, nspec, maxT);
    if (nspec > 0) dfs(0, 0, 0);
    printf("B2-DONE b=%d NMAX=%d part=%d/%d spectra=%d moment_ok=%ld canonical=%ld tested=%ld candidates=%ld lapack_pruned=%ld\n", b, NMAX, PART, NPARTS, nspec, momok, canon, tested, found, lapack_pruned);
    return 0;
}
