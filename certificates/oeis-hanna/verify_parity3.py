#!/usr/bin/env python3
"""Independent exact recomputation and conjecture checks for
A273958, A240998, A295762 (parity conjectures of Paul D. Hanna).

Each sequence is recomputed from its OEIS functional equation with exact
Python integers, compared term-by-term with the downloaded b-file, and the
parity conjecture is checked on (i) every b-file term and (ii) every
recomputed term.  A295762 is additionally recomputed modulo 2^64 with numpy
(exact low 64 bits, hence exact parity) over the full b-file range.
"""
import json, sys, time, os
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))

def bfile(num):
    d = {}
    with open(os.path.join(HERE, 'bfiles', f'b{num}.txt')) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            n, v = line.split()[:2]
            d[int(n)] = int(v)
    return d

def is_pow2(n):
    return n >= 1 and (n & (n - 1)) == 0

def mul_trunc(a, b, N):
    c = [0] * (N + 1)
    for i, x in enumerate(a):
        if x == 0 or i > N:
            continue
        lim = N - i
        for j, y in enumerate(b[:lim + 1]):
            if y:
                c[i + j] += x * y
    return c

report = {}

# ---------- A273958: x*A + x^2*A^2 = C^2, C = x + C^2 ----------
def a273958(N):
    # C = x + C^2, c0 = 0  => c_n = Catalan(n-1)
    c = [0] * (N + 3)
    c[1] = 1
    for n in range(2, N + 3):
        c[n] = sum(c[i] * c[n - i] for i in range(1, n))
    C2 = [sum(c[i] * c[n - i] for i in range(0, n + 1)) for n in range(N + 3)]
    a = [0] * (N + 1)
    A2 = [0] * (N + 1)
    # coefficient of x^m: a_{m-1} + [x^{m-2}] A^2 = [x^m] C^2
    for m in range(1, N + 2):
        s = sum(a[i] * a[m - 2 - i] for i in range(0, m - 1)) if m >= 2 else 0
        a[m - 1] = C2[m] - s
    return a

t = time.time()
N = 1200
a = a273958(N)
b = bfile(273958)
mism = [n for n in b if n <= N and b[n] != a[n]]
conj = lambda n: (n + 1) & (n + 1 - 1) == 0 and n + 1 >= 2 and ((n + 1).bit_length() - 1) % 2 == 1  # n+1 = 2*4^k
viol_b = [n for n in b if (b[n] % 2 == 1) != conj(n)]
viol_r = [n for n in range(1, N + 1) if (a[n] % 2 == 1) != conj(n)]
report['A273958'] = dict(recomputed_terms=N, bfile_terms=len(b), bfile_range=[min(b), max(b)],
                         mismatches_vs_bfile=mism[:10], conj_violations_bfile=viol_b[:10],
                         conj_violations_recomputed=viol_r[:10],
                         odd_indices_recomputed=[n for n in range(1, N + 1) if a[n] % 2],
                         seconds=round(time.time() - t, 2))
print('A273958', report['A273958']['mismatches_vs_bfile'], report['A273958']['conj_violations_bfile'],
      report['A273958']['conj_violations_recomputed'], report['A273958']['odd_indices_recomputed'], flush=True)

# ---------- A240998: A(x)^2 = x + A(x + 2x^2), a(0) = 1 ----------
def a240998(N):
    a = [0] * (N + 1)
    a[0] = 1
    for n in range(1, N + 1):
        # RHS: [n==1] + sum_{k<=n} a_k * C(k, n-k) * 2^(n-k);  the k=n term is a_n
        rhs = (1 if n == 1 else 0)
        for k in range((n + 1) // 2, n):
            rhs += a[k] * comb(k, n - k) * (1 << (n - k))
        # LHS: 2*a_0*a_n + sum_{i=1}^{n-1} a_i a_{n-i}
        lhs_rest = sum(a[i] * a[n - i] for i in range(1, n))
        # 2 a_n + lhs_rest = rhs + a_n  => a_n = rhs - lhs_rest
        a[n] = rhs - lhs_rest
    return a

t = time.time()
N = 1000
a = a240998(N)
b = bfile(240998)
mism = [n for n in b if n <= N and b[n] != a[n]]
viol_b = [n for n in b if n > 0 and (b[n] % 2 == 1) != is_pow2(n)]
viol_r = [n for n in range(1, N + 1) if (a[n] % 2 == 1) != is_pow2(n)]
report['A240998'] = dict(recomputed_terms=N, bfile_terms=len(b), bfile_range=[min(b), max(b)],
                         mismatches_vs_bfile=mism[:10], conj_violations_bfile=viol_b[:10],
                         conj_violations_recomputed=viol_r[:10], seconds=round(time.time() - t, 2),
                         digits_of_last_term=len(str(abs(a[N]))))
print('A240998', report['A240998'], flush=True)

# ---------- A295762: A(x - 2*A(x^2)) = x + A(x^2) ----------
def a295762_exact(N):
    a = [0] * (N + 1)
    a[1] = 1
    known = 1
    while known < N:
        M = min(N, 2 * known + 1)
        # u = x - 2*A(x^2) known exactly up to x^(2*known+1) >= x^M
        u = [0] * (M + 1)
        u[1] = 1
        for j in range(1, known + 1):
            if 2 * j <= M:
                u[2 * j] -= 2 * a[j]
        v = [0] * (M + 1)
        v[1] = 1
        for j in range(1, known + 1):
            if 2 * j <= M:
                v[2 * j] += a[j]
        # compute a_n for n in (known, M] by recursion a_n = v_n - sum_{k<n} a_k [x^n] u^k
        # need powers of u; recompute all a_n, n<=M, from scratch for simplicity
        pw = [1] + [0] * M      # u^0
        pows = []
        cur = pw
        for k in range(1, M + 1):
            cur = mul_trunc(cur, u, M)
            pows.append(cur)
        for n in range(2, M + 1):
            s = sum(a[k] * pows[k - 1][n] for k in range(1, n))
            a[n] = v[n] - s
        known = M
    return a

t = time.time()
N = 260
a = a295762_exact(N)
b = bfile(295762)
mism = [n for n in b if n <= N and b[n] != a[n]]
viol_b = [n for n in b if (b[n] % 2 == 1) != is_pow2(n)]
viol_r = [n for n in range(1, N + 1) if (a[n] % 2 == 1) != is_pow2(n)]
report['A295762'] = dict(recomputed_terms_exact=N, bfile_terms=len(b), bfile_range=[min(b), max(b)],
                         mismatches_vs_bfile=mism[:10], conj_violations_bfile=viol_b[:10],
                         conj_violations_recomputed=viol_r[:10], seconds=round(time.time() - t, 2))
print('A295762', report['A295762'], flush=True)

with open(os.path.join(HERE, 'verify_parity3.json'), 'w') as f:
    json.dump(report, f, indent=1)
