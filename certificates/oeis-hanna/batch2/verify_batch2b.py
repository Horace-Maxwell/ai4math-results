#!/usr/bin/env python3
"""Numerics for A388734 (exact recomputation from the FE) and A338633/A338634
(continued fraction: (i) the b-file values satisfy 1 = A - x/T1, T_k = A - (k+1)^e x / T_{k+1}
modulo two primes to the full b-file precision; (ii) independent recomputation of the first
60 terms from the continued fraction modulo 2^61-1 and modulo 2^64; (iii) parity check)."""
import json, os, time
HERE = os.path.dirname(os.path.abspath(__file__))
BF = os.path.join(HERE, '..', 'bfiles')

def bfile(num):
    d = {}
    for line in open(os.path.join(BF, f'b{num:06d}.txt')):
        line = line.strip()
        if line and not line.startswith('#'):
            n, v = line.split()[:2]
            d[int(n)] = int(v)
    return d

pow2 = lambda n: n >= 1 and n & (n - 1) == 0
report = {}

# A388734: A = 1 + x A^2 + x^2 (1-x) A^3
t = time.time(); N = 1000
a = [0] * (N + 1); A2 = [0] * (N + 1); A3 = [0] * (N + 1)
a[0] = 1; A2[0] = 1; A3[0] = 1
for n in range(1, N + 1):
    v = A2[n - 1]
    if n >= 2: v += A3[n - 2]
    if n >= 3: v -= A3[n - 3]
    a[n] = v
    A2[n] = sum(a[i] * a[n - i] for i in range(n + 1))
    A3[n] = sum(A2[i] * a[n - i] for i in range(n + 1))
b = bfile(388734)
report['A388734'] = dict(terms=N, bfile_terms=len(b), mismatches=[n for n in b if n <= N and a[n] != b[n]][:10],
                         even_terms_recomputed=[n for n in range(N + 1) if a[n] % 2 == 0][:10],
                         even_terms_bfile=[n for n in b if b[n] % 2 == 0][:10], seconds=round(time.time() - t, 1))
print('A388734', report['A388734'], flush=True)

def inv_series(s, N, p):
    # s[0] invertible mod p
    inv0 = pow(s[0] % p, -1, p)
    r = [0] * N
    r[0] = inv0
    for n in range(1, N):
        acc = 0
        for k in range(1, n + 1):
            if s[k]:
                acc += s[k] * r[n - k]
        r[n] = (-acc * inv0) % p
    return r

def mul(a, b, N, p):
    c = [0] * N
    for i in range(N):
        if a[i]:
            ai = a[i]
            for j in range(N - i):
                c[i + j] += ai * b[j]
    return [x % p for x in c]

def cf_check(A, e, N, p):
    # returns max index m < N such that 1 = A - x/T1 holds mod x^N (list of mismatching coefficients)
    A = [x % p for x in A[:N]]
    T = A[:]                       # T_D = A at depth D = N (enough: each level adds a factor x)
    for k in range(N, 0, -1):      # T_k = A - (k+1)^e x / T_{k+1}
        inv = inv_series(T, N, p)
        c = pow(k + 1, e, p)
        xinv = [0] + inv[:N - 1]
        T = [(A[i] - c * xinv[i]) % p for i in range(N)]
    inv = inv_series(T, N, p)
    rhs = [(A[i] - ([0] + inv[:N - 1])[i]) % p for i in range(N)]
    return [i for i in range(N) if rhs[i] != (1 if i == 0 else 0)]

def cf_solve(e, N, p):
    # independent recomputation: a_n = [x^(n-1)] 1/T1 with T1 built from a_0..a_{n-1}
    A = [1] + [0] * (N - 1)
    for n in range(1, N):
        M = n + 1
        Acur = A[:M]
        T = Acur[:]
        for k in range(M, 0, -1):
            inv = inv_series(T, M, p)
            c = pow(k + 1, e, p)
            T = [(Acur[i] - c * ([0] + inv[:M - 1])[i]) % p for i in range(M)]
        inv = inv_series(T, M, p)
        A[n] = inv[n - 1] % p
    return A

for name, num, e in (('A338633', 338633, 3), ('A338634', 338634, 4)):
    t = time.time()
    b = bfile(num); N = max(b) + 1
    A = [b[i] for i in range(N)]
    res = {}
    for p in (1000000007, 998244353):
        res[f'cf_equation_mismatch_mod_{p}'] = cf_check(A, e, N, p)[:10]
    M = 60
    for p in (2 ** 61 - 1, 2 ** 64):
        sol = cf_solve(e, M, p)
        res[f'independent_first_{M}_mismatch_mod_{p}'] = [i for i in range(M) if sol[i] != b[i] % p][:10]
    res['parity_violations_bfile'] = [n for n in b if n > 0 and (b[n] % 2 == 1) != pow2(n)][:10]
    res['bfile_terms'] = len(b); res['seconds'] = round(time.time() - t, 1)
    report[name] = res
    print(name, res, flush=True)

json.dump(report, open(os.path.join(HERE, 'verify_batch2b.json'), 'w'), indent=1)
