#!/usr/bin/env python3
"""A107099: A(A(x)) = x + 4x^3, A = sum a(n) x^(2n+1).
(i) the b-file (n = 0..433, degrees <= 867) satisfies A(A(x)) = x + 4x^3 modulo two primes;
(ii) coefficient pattern modulo 3: zero off powers of 3; values at 3^k."""
import numpy as np, json, os, time
HERE = os.path.dirname(os.path.abspath(__file__))
b = {}
for line in open(os.path.join(HERE, '..', 'bfiles', 'b107099.txt')):
    line = line.strip()
    if line and not line.startswith('#'):
        n, v = line.split()[:2]; b[int(n)] = int(v)
N = 2 * max(b) + 2          # degrees 0..867
res = {}
t = time.time()
for p in (1048573, 1048571):
    A = np.zeros(N, dtype=np.int64)
    for n, v in b.items():
        A[2 * n + 1] = v % p
    r = np.zeros(N, dtype=np.int64)
    for k in range(N - 1, -1, -1):       # Horner: A(A(x))
        r = np.convolve(r, A)[:N] % p
        r[0] = (r[0] + A[k]) % p
    target = np.zeros(N, dtype=np.int64); target[1] = 1; target[3] = 4 % p
    res[f'equation_mismatch_mod_{p}'] = [int(i) for i in np.nonzero((r - target) % p)[0][:10]]
coef = {2 * n + 1: v for n, v in b.items()}
pw = {3 ** j for j in range(8)}
res['nonzero_mod3_off_powers_of_3'] = [d for d in sorted(coef) if coef[d] % 3 and d not in pw][:10]
res['mod3_at_powers_of_3'] = {d: coef[d] % 3 for d in sorted(pw) if d in coef}
res['degrees_checked'] = [min(coef), max(coef)]
res['seconds'] = round(time.time() - t, 1)
print(res)
json.dump(res, open(os.path.join(HERE, 'verify_a107099.json'), 'w'), indent=1)
