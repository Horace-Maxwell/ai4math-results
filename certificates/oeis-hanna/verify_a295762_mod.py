#!/usr/bin/env python3
"""Recompute A295762 from A(x - 2*A(x^2)) = x + A(x^2) over the full b-file range
(n <= 1030) modulo 2^64 (numpy uint64 wraparound; gives the exact parity) and modulo the
primes 16777213 and 33554393, and compare with the b-file.  Exact big-integer recomputation
of the first 260 terms is in verify_parity3.py."""
import numpy as np, json, os, time
HERE = os.path.dirname(os.path.abspath(__file__))
b = {}
for line in open(os.path.join(HERE, 'bfiles', 'b295762.txt')):
    line = line.strip()
    if line and not line.startswith('#'):
        n, v = line.split()[:2]; b[int(n)] = int(v)
N = max(b)
def run(mod):
    dt = np.uint64 if mod is None else np.int64
    red = (lambda x: x) if mod is None else (lambda x: np.mod(x, mod))
    a = np.zeros(N + 1, dtype=dt); a[1] = 1
    known = 1
    while known < N:
        M = min(N, 2 * known + 1)
        u = np.zeros(M + 1, dtype=dt); v = np.zeros(M + 1, dtype=dt)
        u[1] = 1; v[1] = 1
        for j in range(1, known + 1):
            if 2 * j <= M:
                if mod is None:
                    u[2 * j] = u[2 * j] - np.uint64(2) * a[j]
                else:
                    u[2 * j] = (u[2 * j] - 2 * a[j]) % mod
                v[2 * j] = red(v[2 * j] + a[j])
        P = np.zeros((M + 1, M + 1), dtype=dt)   # P[k] = u^k truncated
        cur = np.zeros(M + 1, dtype=dt); cur[0] = 1
        for k in range(1, M + 1):
            cur = red(np.convolve(cur, u)[:M + 1]); P[k] = cur
        for n in range(2, M + 1):
            s = red(np.dot(a[1:n], P[1:n, n])) if mod is not None else np.dot(a[1:n], P[1:n, n])
            a[n] = red(v[n] - s) if mod is not None else v[n] - s
        known = M
    return a
t = time.time()
res = {}
a64 = run(None)
res['mod2^64_mismatches'] = [n for n in b if int(a64[n]) != b[n] % 2**64][:10]
res['parity_conj_violations_recomputed'] = [n for n in range(1, N + 1) if (int(a64[n]) & 1) != (1 if n & (n - 1) == 0 else 0)][:10]
for p in (16777213, 33554393):
    ap = run(p)
    res[f'mod{p}_mismatches'] = [n for n in b if int(ap[n]) != b[n] % p][:10]
res['N'] = N; res['seconds'] = round(time.time() - t, 1)
print(res)
json.dump(res, open(os.path.join(HERE, 'verify_a295762_mod.json'), 'w'), indent=1)
