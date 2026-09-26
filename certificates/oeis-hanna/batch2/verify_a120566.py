#!/usr/bin/env python3
"""A120566: A = A(A(x)) - x*A(A(A(x))), a0 = 0, a1 = 1.
(i) b-file values satisfy the equation modulo two primes to full precision (500 terms);
(ii) independent recomputation of 150 terms via the contraction A <- 2A - Phi(A),
     modulo 2^64 and modulo a prime; (iii) parity of all b-file terms."""
import numpy as np, json, os, time
HERE = os.path.dirname(os.path.abspath(__file__))
b = {}
for line in open(os.path.join(HERE, '..', 'bfiles', 'b120566.txt')):
    line = line.strip()
    if line and not line.startswith('#'):
        n, v = line.split()[:2]; b[int(n)] = int(v)
def comp(A, B, N, mod):
    # A(B(x)) truncated to degree < N; A, B arrays of length N with B[0] = 0
    r = np.zeros(N, dtype=np.int64 if mod else np.uint64)
    for k in range(N - 1, -1, -1):
        r = np.convolve(r, B)[:N]
        if mod: r %= mod
        r[0] += A[k]
        if mod: r %= mod
    return r
def phi(A, N, mod):
    AA = comp(A, A, N, mod)
    AAA = comp(A, AA, N, mod)
    xAAA = np.zeros_like(AAA); xAAA[1:] = AAA[:N - 1]
    r = AA - xAAA
    return r % mod if mod else r
res = {}
t = time.time()
N = max(b) + 1
for p in (1048573, 1048571):
    A = np.array([0] + [b[i] % p for i in range(1, N)], dtype=np.int64)
    d = (phi(A, N, p) - A) % p
    res[f'bfile_equation_mismatch_mod_{p}'] = [int(i) for i in np.nonzero(d)[0][:10]]
M = 150
for mod in (None, 1048573):
    A = np.zeros(M, dtype=np.int64 if mod else np.uint64); A[1] = 1
    for it in range(M):
        A = (2 * A - phi(A, M, mod))
        if mod: A %= mod
        A[0] = 0; A[1] = 1
    ref = np.array([0] + [b[i] % (mod if mod else 2**64) for i in range(1, M)], dtype=np.int64 if mod else np.uint64)
    res[f'independent_{M}_mismatch_mod_{mod or "2^64"}'] = [int(i) for i in np.nonzero(A != ref)[0][:10]]
res['even_terms_bfile'] = [n for n in b if b[n] % 2 == 0][:10]
res['bfile_terms'] = len(b); res['seconds'] = round(time.time() - t, 1)
print(res)
json.dump(res, open(os.path.join(HERE, 'verify_a120566.json'), 'w'), indent=1)
