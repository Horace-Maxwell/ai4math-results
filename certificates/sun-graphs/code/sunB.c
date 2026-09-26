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
 * Usage: sunB b NMAX
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef long long ll;
typedef unsigned __int128 u128;

static int b, NMAX;
static int pp[64], qq[64];
static const uint64_t PRIMES[3] = {1000000007ULL, 998244353ULL, 2305843009213693951ULL};

/* spectra: T4 = sum_{|l|>=2} l^2(l^2-1) (over B+ for even b; over B+ and B- for odd b), S2 = sum l^2 */
static ll specT[100000], specS[100000], specN[100000]; static int nspec = 0;
static int PART = 0, NPARTS = 1;
static int cpos[10], cneg[10];
static ll powll(ll v, int e) { ll r = 1; for (int i = 0; i < e; i++) r *= v; return r; }
static int cGT = -1, cLT = -1;   /* eigenvalues of C_b above 1 / below -1 */
static void record(void) {
    ll T = 0, S = 0;
    if (cGT < 0) {
        cGT = 0; cLT = 0;
        for (int j = 0; j < b; j++) {
            if (j * 6 < b || (b - j) * 6 < b) cGT++;          /* angle 2 pi j/b within pi/3 of 0 */
            if (3 * (2 * j - b) < b && 3 * (b - 2 * j) < b) cLT++;   /* within pi/3 of pi */
        }
    }
    { int np = 0, nm = 0; for (int v = 2; v <= 9; v++) { np += cpos[v]; nm += cneg[v]; }
      if (np < cGT) return;
      if (b % 2 == 1 && nm < cLT) return; }
    for (int v = 2; v <= 9; v++) { T += (ll)(cpos[v] + cneg[v]) * v * v * (v * v - 1); S += (ll)(cpos[v] + cneg[v]) * v * v; }
    if (b % 2 == 0) { if (S > NMAX) return; }
    else {
        if (S > 2LL * NMAX) return;
        for (int L = 3; L <= b; L += 2) {          /* closed odd walks: tr A^L = 0 (L<b), 2b (L=b) */
            ll s = 0; for (int v = 2; v <= 9; v++) s += (ll)(cpos[v] - cneg[v]) * (powll(v, L) - v);
            if (s != (L == b ? 2LL * b : 0)) return;
        }
    }
    { int np = 0; for (int v = 2; v <= 9; v++) np += cpos[v]; specN[nspec] = np; }
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
            if (a1 > a0) return 0;            /* v3: canonical = lexicographically GREATEST image */
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
    int ok = 0;
    for (int i = 0; i < nspec && !ok; i++) {
        if (specT[i] != T || specS[i] < lo || specS[i] > hi) continue;
        if (b % 2 == 0) {   /* count identity: mult(0) = 2 S2 - n - 2|B+| must lie in [0, max(P,2)] */
            ll m0 = 2 * specS[i] - n - 2 * specN[i], mp = P > 2 ? P : 2;
            if (m0 < 0 || m0 > mp) continue;
        }
        ok = 1;
    }
    if (!ok) return;
    momok++;
    if (!canonical()) return;
    canon++;
    for (int ip = 0; ip < 3; ip++) if (rootsum_mod(PRIMES[ip]) < 4 * b) { tested++; return; }
    tested++; found++;
    printf("CANDIDATE b=%d n=%d :", b, n); for (int k = 0; k < b; k++) printf(" (%d,%d)", pp[k], qq[k]); printf("\n"); fflush(stdout);
}
static void dfs(int k, int W, ll M, int Pc, int Qc) {
    int rem = NMAX - b - W;
    if (k == b) { leaf(); return; }
    ll lastT = (b % 2 == 0) ? maxT - (b == 4 ? 4 : 0) : maxT / 2;
    for (int q = 0; 2 * q <= rem; q++) for (int p = 0; p + 2 * q <= rem; p++) {
        ll d = 2 + p + q; ll M2 = M + d * (d - 1) + 2LL * q;
        if (M2 + 2LL * (b - k - 1) > lastT) break;   /* increasing in p */
        if (k >= 1 && p * 1000 + q > pp[0] * 1000 + qq[0]) break;   /* vertex 0 has a maximal key */
        if (k == 0 && ((p * 1000 + q) % NPARTS) != PART) continue;
        {   /* per admissible spectrum: reachable 4th-moment window [M2 + 2r, M2 + g(w') + 2(r-1)],
               g(w) = (2+w)(1+w), r vertices left; for even b also the count identities
               mult(0) = 2 S2 - n - 2|B+| in [0, max(P,2)],  mult(1) = n - S2 >= 0          */
            ll r = b - k - 1, wl = rem - p - 2 * q;
            ll lo = M2 + 2 * r, hi = (r > 0) ? M2 + (2 + wl) * (1 + wl) + 2 * (r - 1) : M2;
            ll Pn = Pc + p, Qn = Qc + q, Wn = W + p + 2 * q;
            int hit = 0;
            for (int i = 0; i < nspec && !hit; i++) {
                ll t = (b % 2 == 0) ? specT[i] - (b == 4 ? 4 : 0) : specT[i] / 2;
                if (t < lo || t > hi) continue;
                if (b % 2 == 0) {
                    ll S2 = specS[i], sN = specN[i];
                    ll nmin = b + Wn, nmax = NMAX;
                    if (nmin < S2) nmin = S2;                       /* mult(1) = n - S2 >= 0 */
                    if (nmax > 2 * S2 - 2 * sN) nmax = 2 * S2 - 2 * sN; /* mult(0) >= 0 */
                    if (nmin > nmax) continue;
                    if (Pn >= 2 && 2 * Qn > 2 * nmax - b - 2 * S2 + 2 * sN) continue; /* mult(0) <= P */
                }
                hit = 1;
            }
            if (!hit) continue;
        }
        pp[k] = p; qq[k] = q;
        dfs(k + 1, W + p + 2 * q, M2, Pc + p, Qc + q);
    }
}
int main(int argc, char **argv) {
    b = atoi(argv[1]); NMAX = atoi(argv[2]); if (argc >= 5) { PART = atoi(argv[3]); NPARTS = atoi(argv[4]); }
    recpos(2);
    for (int i = 0; i < nspec; i++) if (specT[i] > maxT) maxT = specT[i];
    fprintf(stderr, "B: b=%d NMAX=%d spectra=%d maxT=%lld\n", b, NMAX, nspec, maxT);
    if (nspec > 0) dfs(0, 0, 0, 0, 0);
    printf("B-DONE b=%d NMAX=%d part=%d/%d spectra=%d moment_ok=%ld canonical=%ld tested=%ld candidates=%ld\n", b, NMAX, PART, NPARTS, nspec, momok, canon, tested, found);
    return 0;
}
