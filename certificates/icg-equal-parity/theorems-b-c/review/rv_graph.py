r"""Item 8 (graph level, independent of the sign-matrix model and of Jiang-Yang Prop. 2.2).

For n = p^2 q^b and every set D of proper divisors of n, the eigenvalues of ICG_n(D) are lambda_t = sum_{d in D} c_{n/d}(t)
(Ramanujan sums), and lambda_t depends only on g = gcd(t, n) (class multiplicity phi(n/g)).  Energy is computed exactly:
   E(D) = sum_{g | n} phi(n/g) |sum_{d in D} c_{n/d}(g)|.
c_m(g) via von Sterneck: mu(m/(m,g)) phi(m) / phi(m/(m,g)) with generic trial-division factorisation; cross-checked against the
divisor-sum definition for small n.  For small n the exact energies are also compared with floating-point spectra of the actual
circulant adjacency matrices (FFT of the first row), for ALL divisor sets.
Checks: max energy == 1/2[n + d_2(p) d_b(q)] - delta_2(p) delta_b(q) (Theorem B, and the same value read in the p^b q^2 labelling),
and the maximisers are exactly D- = {p^i q^j: i+j odd}, D+ \ {n} = {p^i q^j: i+j even} \ {n}.
"""
import sys, time, itertools
from fractions import Fraction as Fr
from math import gcd
import numpy as np
from rv_common import d_closed, delta_closed, ramanujan

out = []
def log(s):
    print(s); sys.stdout.flush(); out.append(s)


def factor(n):
    f = {}; d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def phi_f(n):
    r = n
    for pr in factor(n):
        r = r // pr * (pr - 1)
    return r


def mob_f(n):
    f = factor(n)
    if any(e > 1 for e in f.values()):
        return 0
    return (-1) ** len(f)


def c_vs(m, g):
    k = m // gcd(m, g)
    return mob_f(k) * phi_f(m) // phi_f(k)


# cross-check von Sterneck vs divisor sum on small cases
for m in range(1, 80):
    for g in range(0, 80):
        gg = g if g else m * 97  # gcd(m,0)=m: emulate with a multiple of m
        assert c_vs(m, gg) == ramanujan(m, g), (m, g)
log("von Sterneck formula == divisor-sum definition of c_m(t) for m < 80, t < 80: OK")


def run(p, q, b, fft_check=False):
    t0 = time.time()
    n = p * p * q ** b
    divs = sorted(p ** i * q ** j for i in range(3) for j in range(b + 1))
    proper = [d for d in divs if d != n]
    k = len(proper)
    C = np.array([[c_vs(n // d, g) for g in divs] for d in proper], dtype=np.int64)       # k x tau
    w = np.array([phi_f(n // g) for g in divs], dtype=np.int64)
    Dm = {p ** i * q ** j for i in range(3) for j in range(b + 1) if (i + j) % 2 == 1}
    Dp = {p ** i * q ** j for i in range(3) for j in range(b + 1) if (i + j) % 2 == 0} - {n}
    best = None; arg = []
    chunk = 1 << 16
    total = 1 << k
    bitsidx = np.arange(k)
    for start in range(0, total, chunk):
        idx = np.arange(start, min(total, start + chunk), dtype=np.int64)
        X = (idx[:, None] >> bitsidx) & 1
        lam = X @ C                                   # chunk x tau (exact ints)
        E = np.abs(lam) @ w
        E[idx == 0] = -1                              # exclude the empty set (not a valid D); energy 0 anyway
        mx = int(E.max())
        if best is None or mx > best:
            best = mx; arg = [int(i) for i in idx[E == mx]]
        elif mx == best:
            arg += [int(i) for i in idx[E == mx]]
    sets = [frozenset(proper[j] for j in range(k) if (a >> j) & 1) for a in arg]
    target2 = n + d_closed(2, p) * d_closed(b, q) - 2 * delta_closed(2, p) * delta_closed(b, q)   # = 2 E_max
    target2_swapped = n + d_closed(b, q) * d_closed(2, p) - 2 * delta_closed(b, q) * delta_closed(2, p)
    ok = (Fr(2 * best) == target2) and set(sets) == {frozenset(Dm), frozenset(Dp)} and len(sets) == 2
    msg = (f"n = {p}^2*{q}^{b} = {n}: {total - 1} divisor sets; max E = {best}, formula = {target2 / 2} "
           f"(p^b q^2 reading: {target2_swapped / 2}); match={Fr(2 * best) == target2}; maximisers == {{D-, D+\\{{n}}}}: "
           f"{set(sets) == {frozenset(Dm), frozenset(Dp)} and len(sets) == 2}")
    if fft_check:
        # compare with FFT spectra of the actual circulant adjacency matrices, all divisor sets
        tgcd = np.array([gcd(t, n) for t in range(n)])
        maxdiff = 0.0
        for a in range(1, total):
            D = [proper[j] for j in range(k) if (a >> j) & 1]
            row = np.isin(tgcd, D).astype(float)
            row[0] = 0.0
            ev = np.fft.fft(row).real
            Ef = np.abs(ev).sum()
            lam = sum(C[j] for j in range(k) if (a >> j) & 1)
            Ex = int(np.abs(lam) @ w)
            maxdiff = max(maxdiff, abs(Ef - Ex))
        msg += f"; FFT spectra vs exact energies over all sets: max |diff| = {maxdiff:.2e}"
        ok &= maxdiff < 1e-6
    log(msg + f" ({time.time() - t0:.1f}s)")
    return ok


allok = True
for (p, q) in [(3, 5), (3, 7), (5, 7), (3, 11), (5, 11), (7, 11), (3, 13), (11, 13)]:
    allok &= run(p, q, 2, fft_check=(p * p * q * q <= 1300))
for (p, q) in [(3, 5), (5, 3), (3, 7), (7, 3), (5, 7), (7, 5), (3, 11), (11, 3), (13, 3)]:
    allok &= run(p, q, 4, fft_check=(p * p * q ** 4 <= 6000))
for (p, q) in [(3, 5), (5, 3), (7, 3), (3, 7)]:
    allok &= run(p, q, 6)
log(f"ALL {'OK' if allok else 'NOT OK'}")
