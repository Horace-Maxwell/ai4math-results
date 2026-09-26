#!/usr/bin/env python3
"""Batch-2 numerics: recompute each sequence from its OEIS functional equation (independently
of the b-file), compare with the b-file, and test the conjecture.

A377100  A(x) = A(x^3)/A(x^2) + A(x)^2                      exact integers, 1200 terms
A274479  A(x)^2 = A(x^2/(1-2x-4x^2))                         exact integers, 300 terms
A301933  A = x(1+4AA')/(1+AA')                               exact integers, 400 terms
A091713  A = x + x A(A(A(x)))                                mod 2^64 and mod p, 400 terms
A196523  A = x + x A(A(A(A(x))))                             mod 2^64 and mod p, 400 terms
A184894  a(m) = [x^(2m-1)] of the m-th iterate of x+x^3       exact (m<=18), mod 3 and mod 9 (m<=400)
A107099  A(A(x)) = x + 4x^3                                   b-file inspection mod 3
"""
import json, os, time
import numpy as np
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

report = {}

# ---------------- A377100 ----------------
def a377100(N):
    # cleared form: A(x^2) * (A - A^2) = A(x^3), a0 = 0, a1 = 1
    a = [0] * (N + 1); a[1] = 1
    sq = [0] * (N + 1)      # coefficients of A^2
    B = [0] * (N + 1)       # coefficients of A - A^2
    B[1] = 1
    for n in range(2, N + 1):
        sq[n] = sum(a[i] * a[n - i] for i in range(1, n))
        # coefficient x^(n+2):  sum_{i>=1} a_i * B_{n+2-2i} = [3 | n+2] a_{(n+2)/3}
        rhs = a[(n + 2) // 3] if (n + 2) % 3 == 0 else 0
        rest = sum(a[i] * B[n + 2 - 2 * i] for i in range(2, (n + 1) // 2 + 1))
        # i = 1 term: B_n = a_n - sq_n
        a[n] = rhs - rest + sq[n]
        B[n] = a[n] - sq[n]
    return a

t = time.time(); N = 1200
a = a377100(N); b = bfile(377100)
report['A377100'] = dict(terms=N, bfile_terms=len(b), mismatches=[n for n in b if n <= N and a[n] != b[n]][:10],
                         violations=[n for n in range(1, N + 1) if a[n] % 3 != 1][:10], seconds=round(time.time() - t, 1))
print('A377100', report['A377100'], flush=True)

# ---------------- A274479 ----------------
def a274479(N):
    # A^2 = A(h), h = x^2/(1-2x-4x^2); a0 = 0, a1 = 1; coefficient n+1 of A^2 contains 2 a1 a_n
    M = N + 1
    h = [0] * (M + 1)
    # h*(1-2x-4x^2) = x^2
    for n in range(M + 1):
        v = (1 if n == 2 else 0)
        if n >= 1: v += 2 * h[n - 1]
        if n >= 2: v += 4 * h[n - 2]
        h[n] = v
    pw = {0: [1] + [0] * M}
    cur = pw[0]
    for k in range(1, M // 2 + 1):
        nxt = [0] * (M + 1)
        for i, x in enumerate(cur):
            if x:
                for j in range(0, M + 1 - i):
                    if h[j]: nxt[i + j] += x * h[j]
        pw[k] = nxt; cur = nxt
    a = [0] * (N + 1); a[1] = 1
    for n in range(2, N + 1):
        m = n + 1      # compare coefficient of x^(n+1)
        rhs = sum(a[k] * pw[k][m] for k in range(1, m // 2 + 1) if k <= N)
        rest = sum(a[i] * a[m - i] for i in range(2, m - 1))
        num = rhs - rest
        assert num % 2 == 0
        a[n] = num // 2
    return a

t = time.time(); N = 300
a = a274479(N); b = bfile(274479)
report['A274479'] = dict(terms=N, bfile_terms=len(b), mismatches=[n for n in b if n <= N and a[n] != b[n]][:10],
                         violations=[n for n in range(1, N + 1) if a[n] % 3 != 1][:10], seconds=round(time.time() - t, 1))
print('A274479', report['A274479'], flush=True)

# ---------------- A301933 ----------------
def a301933(N):
    # A + A*P = x + 4 x P, P = A*A'
    a = [0] * (N + 2); P = [0] * (N + 2)
    for n in range(1, N + 1):
        AP = sum(a[i] * P[n - i] for i in range(1, n))
        a[n] = (1 if n == 1 else 0) + 4 * P[n - 1] - AP
        P[n] = sum(a[i] * (n - i + 1) * a[n - i + 1] for i in range(1, n + 1))
    return a

t = time.time(); N = 400
a = a301933(N); b = bfile(301933)
pow2 = lambda n: n >= 1 and n & (n - 1) == 0
report['A301933'] = dict(terms=N, bfile_terms=len(b), mismatches=[n for n in b if n <= N and a[n] != b[n]][:10],
                         violations=[n for n in range(1, N + 1) if (a[n] % 2 == 1) != pow2(n)][:10], seconds=round(time.time() - t, 1))
print('A301933', report['A301933'], flush=True)

# ---------------- iterated composition A = x (1 + A^{l}(x))  (Manyama recurrence, independent of b-file) ----
def iter_eq(N, l, mod):
    # T[k][n] = [x^n] A^{k}(x), A^{k} = A^{k-1} (1 + A^{k+l-1});  A^0 = x
    Kmax = 1 + (N - 1) * (l - 1) + l
    T = [[0] * (N + 1) for _ in range(Kmax + l + 1)]
    for k in range(len(T)):
        T[k][1] = 1
    for n in range(2, N + 1):
        K = 1 + (N - n) * (l - 1)
        for k in range(1, K + 1):
            s = T[k - 1][n]
            up = T[k + l - 1]; lo = T[k - 1]
            for j in range(1, n):
                s += up[j] * lo[n - j]
            T[k][n] = s % mod
    return [T[1][n] for n in range(N + 1)]

for name, num, l, N in (('A091713', 91713, 3, 400), ('A196523', 196523, 4, 400)):
    t = time.time()
    b = bfile(num)
    res = {}
    for mod in (2 ** 64, 1000000007):
        a = iter_eq(N, l, mod)
        res[f'mismatches_mod_{mod}'] = [n for n in b if n <= N and a[n] != b[n] % mod][:10]
        if mod == 2 ** 64:
            if l == 3:
                res['violations_recomputed'] = [n for n in range(1, N + 1) if a[n] % 2 != 1][:10]
            else:
                res['violations_recomputed'] = [n for n in range(1, N + 1) if a[n] % 3 != 1 % 3 or False][:0]
                # mod 2^64 does not give residues mod 3; use the prime run below instead
    if l == 4:
        a3 = iter_eq(N, l, 3)
        res['violations_recomputed_mod3'] = [n for n in range(1, N + 1) if a3[n] != 1][:10]
    res['violations_bfile'] = ([n for n in b if b[n] % 2 != 1][:10] if l == 3 else [n for n in b if b[n] % 3 != 1][:10])
    res['terms'] = N; res['bfile_terms'] = len(b); res['seconds'] = round(time.time() - t, 1)
    report[name] = res
    print(name, res, flush=True)

# ---------------- A184894 ----------------
t = time.time()
b = bfile(184894)
# exact for m <= 18
def iterates_exact(M):
    deg = 2 * M - 1
    p = [0] * (deg + 1); p[1] = 1
    out = {}
    for m in range(1, M + 1):
        # p <- p + p^3 truncated (g o p with g = x + x^3)
        sq = [0] * (deg + 1)
        for i, x in enumerate(p):
            if x:
                for j in range(0, deg + 1 - i):
                    if p[j]: sq[i + j] += x * p[j]
        cu = [0] * (deg + 1)
        for i, x in enumerate(sq):
            if x:
                for j in range(0, deg + 1 - i):
                    if p[j]: cu[i + j] += x * p[j]
        p = [p[i] + cu[i] for i in range(deg + 1)]
        out[m] = p[2 * m - 1]
    return out
ex = iterates_exact(18)
res = dict(exact_mismatches=[m for m in b if ex.get(m) != b[m]])
def iterates_mod(M, mod):
    deg = 2 * M - 1
    p = np.zeros(deg + 1, dtype=np.int64); p[1] = 1
    out = {}
    for m in range(1, M + 1):
        sq = np.convolve(p, p)[:deg + 1] % mod
        cu = np.convolve(sq, p)[:deg + 1] % mod
        p = (p + cu) % mod
        out[m] = int(p[2 * m - 1])
    return out
M = 400
r3 = iterates_mod(M, 3); r9 = iterates_mod(M, 9)
nonzero3 = [m for m in range(1, M + 1) if r3[m] != 0]
res['nonzero_mod3_positions_upto_400'] = nonzero3
res['residue_mod3_at_365'] = r3[365]; res['residue_mod9_at_365'] = r9[365]
res['values_mod3_at_(3^j+1)/2'] = {(3 ** j + 1) // 2: r3[(3 ** j + 1) // 2] for j in range(0, 7)}
res['consistency_mod3_vs_exact'] = [m for m in range(1, 19) if ex[m] % 3 != r3[m]]
res['seconds'] = round(time.time() - t, 1)
report['A184894'] = res
print('A184894', res, flush=True)

# ---------------- A107099 (b-file) ----------------
b = bfile(107099)
res = {}
res['bfile_range'] = [min(b), max(b)]
res['coef_x^(3^j)_mod3'] = {3 ** j: b[(3 ** j - 1) // 2] % 3 for j in range(0, 7) if (3 ** j - 1) // 2 in b}
res['nonzero_mod3_at_nonpowers'] = [2 * n + 1 for n in b if b[n] % 3 and not any(2 * n + 1 == 3 ** j for j in range(10))][:10]
report['A107099'] = res
print('A107099', res, flush=True)

json.dump(report, open(os.path.join(HERE, 'verify_batch2.json'), 'w'), indent=1)
