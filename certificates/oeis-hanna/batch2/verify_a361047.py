#!/usr/bin/env python3
"""A361047: A(x - x^3*A'(x)^2) = x with A = sum a(n) x^(2n-1).
(i) the b-file (n = 1..301, degrees <= 601) satisfies the equation modulo two primes;
(ii) independent recomputation of 60 coefficients modulo a prime by fixed-point iteration;
(iii) coefficient pattern modulo 3 (exponent form)."""
import numpy as np, json, os, time
HERE = os.path.dirname(os.path.abspath(__file__))
b = {}
for line in open(os.path.join(HERE, '..', 'bfiles', 'b361047.txt')):
    line = line.strip()
    if line and not line.startswith('#'):
        n, v = line.split()[:2]; b[int(n)] = int(v)
N = 2 * max(b)            # degrees 0..601
def comp(A, B, N, p):
    r = np.zeros(N, dtype=np.int64)
    for k in range(N - 1, -1, -1):
        r = np.convolve(r, B)[:N] % p
        r[0] = (r[0] + A[k]) % p
    return r
def g_of(A, N, p):
    dA = np.zeros(N, dtype=np.int64)
    for i in range(1, N):
        dA[i - 1] = (i * A[i]) % p
    sq = np.convolve(dA, dA)[:N] % p
    g = np.zeros(N, dtype=np.int64); g[1] = 1
    g[3:] = (g[3:] - sq[:N - 3]) % p
    return g
res = {}; t = time.time()
for p in (1048573, 1048571):
    A = np.zeros(N, dtype=np.int64)
    for n, v in b.items():
        A[2 * n - 1] = v % p
    r = comp(A, g_of(A, N, p), N, p)
    target = np.zeros(N, dtype=np.int64); target[1] = 1
    res[f'equation_mismatch_mod_{p}'] = [int(i) for i in np.nonzero((r - target) % p)[0][:10]]
# independent fixed-point recomputation: A <- A + (x - A(g_A))  (contraction in the x-adic sense)
p = 1048573; M = 60
A = np.zeros(M, dtype=np.int64); A[1] = 1
for it in range(M):
    r = comp(A, g_of(A, M, p), M, p)
    tgt = np.zeros(M, dtype=np.int64); tgt[1] = 1
    A = (A + tgt - r) % p
ref = np.zeros(M, dtype=np.int64)
for n, v in b.items():
    if 2 * n - 1 < M: ref[2 * n - 1] = v % p
res[f'independent_{M}_mismatch_mod_{p}'] = [int(i) for i in np.nonzero(A != ref)[0][:10]]
coef = {2 * n - 1: v for n, v in b.items()}
pw = {3 ** j for j in range(8)}
res['nonzero_mod3_off_powers_of_3'] = [d for d in sorted(coef) if coef[d] % 3 and d not in pw][:10]
res['mod3_at_powers_of_3'] = {d: coef[d] % 3 for d in sorted(pw) if d in coef}
res['literal_conjecture_counterexample_n2'] = {'a(2)': b[2], 'a(2) mod 3': b[2] % 3}
res['degrees_checked'] = [min(coef), max(coef)]; res['seconds'] = round(time.time() - t, 1)
print(res)
json.dump(res, open(os.path.join(HERE, 'verify_a361047.json'), 'w'), indent=1)
