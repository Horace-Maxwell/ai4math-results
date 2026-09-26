import math, itertools
from fractions import Fraction
def primes_upto(m):
    return [q for q in range(2, m+1) if all(q % d for d in range(2, int(q**0.5)+1))]
def kappa(b):
    r = 1
    for q in primes_upto(b):
        if (b-1) % (q-1) == 0: r *= q
    return r
lst = [b for b in range(3, 200, 2) if (2*b) % kappa(b) == 0]
print("odd b<200 with kappa_b | 2b:", lst)
print("kappa 5,7,9,11,13:", [kappa(b) for b in (5,7,9,11,13)])
# von Staudt-Clausen: denominator of B_{b-1} (exact Bernoulli via Akiyama-Tanigawa)
def bernoulli(n):
    A = [Fraction(0)]*(n+1)
    for m in range(n+1):
        A[m] = Fraction(1, m+1)
        for j in range(m, 0, -1):
            A[j-1] = j*(A[j-1] - A[j])
    return A[0]
print("denominator(B_{b-1}) == kappa_b for odd b in 3..61:", all(bernoulli(b-1).denominator == kappa(b) for b in range(3, 62, 2)))
print("sum_{v=2}^8 v^2 =", sum(v*v for v in range(2, 9)))
# N_{>1}(C_b) via floating eigenvalues with a safety margin check
ok = True
for b in range(3, 61):
    ev = [2*math.cos(2*math.pi*j/b) for j in range(b)]
    assert all(abs(e-1) > 1e-9 for e in ev) or b % 6 == 0
    cnt = sum(1 for e in ev if e > 1 + 1e-12)
    if cnt != 2*math.ceil(b/6) - 1: ok = False; print("mismatch", b, cnt)
print("N_{>1}(C_b) = 2ceil(b/6)-1 for b=3..60:", ok)
SEQ = [v*v for v in range(2, 3000) for _ in range(4)]
def sigma(t):
    seq = SEQ
    return sum(seq[:t]) if t > 0 else 0
print("sigma(9,10,11,14) =", [sigma(t) for t in (9,10,11,14)])
for n in (41, 42):
    r = max(t for t in range(0, 40) if sigma(t) <= 2*n); print("r_max(%d) = %d" % (n, r))
# b <= (96 n)^(1/3) + 7 check against b <= r_max(n) + 4 for n up to 10^5
bad = 0
for n in range(3, 100000, 7):
    lo, hi = 0, 10000
    while lo < hi:
        mid = (lo + hi + 1)//2
        if sigma(mid) <= 2*n: lo = mid
        else: hi = mid - 1
    if lo + 4 > (96*n)**(1/3) + 7 + 1e-9: bad += 1
print("r_max(n)+4 <= (96n)^(1/3)+7 violations (n<1e5 step 7):", bad)
# minimal S2 for |B+| = 5, 6 with rho simple and others at most twice
best = {}
for cp in itertools.product(range(3), repeat=8):
    vals = range(2, 10); nz = [v for v, c in zip(vals, cp) if c]
    if not nz: continue
    rho = max(nz)
    if rho < 3 or cp[rho-2] != 1: continue
    s = sum(cp); S2 = sum(c*v*v for v, c in zip(vals, cp))
    best[s] = min(best.get(s, 10**9), S2)
print("min S2 by |B+|:", {s: best[s] for s in sorted(best) if s <= 6})
