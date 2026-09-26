"""Independent spot checks (written for the paper revision) of numerical claims added to note.tex.
Energies are computed from the eigenvalues lambda_t = sum_{d in D} c_{n/d}(t) (Ramanujan sums), not from the T-matrix model."""
from math import gcd
from itertools import combinations
from fractions import Fraction as Fr

def mobius(n):
    r, k = 1, 2
    while k * k <= n:
        if n % k == 0:
            n //= k
            if n % k == 0: return 0
            r = -r
        k += 1
    return -r if n > 1 else r

def ram(m, t):
    g = gcd(m, t) if t else m
    return sum(mobius(m // d) * d for d in range(1, g + 1) if g % d == 0 and m % d == 0)

def energy(n, D):
    return sum(abs(sum(ram(n // d, t) for d in D)) for t in range(n))

def d_closed(k, x):
    return (2 * k + 1) * x ** k + 4 * sum((-1) ** (k - j) * (j + 1) * x ** j for j in range(k))

def delta_closed(k, x):
    return Fr(x ** k * (x - 1) + 2 * (-1) ** k, x + 1)

def proper_divs(n): return [d for d in range(1, n) if n % d == 0]

def emax(n):
    divs = proper_divs(n); best = -1; arg = []
    for r in range(1, len(divs) + 1):
        for D in combinations(divs, r):
            e = energy(n, D)
            if e > best: best, arg = e, [D]
            elif e == best: arg.append(D)
    return best, arg

print("(a) n = pq: energies of the seven nonempty sets")
for p, q in [(3, 5), (5, 3), (3, 7), (5, 7), (7, 11)]:
    n = p * q
    E = {D: energy(n, D) for D in [(1,), (p,), (q,), (1, p), (1, q), (p, q), (1, p, q)]}
    ok = (E[(1,)] == E[(p, q)] == 4 * (p - 1) * (q - 1) and E[(p,)] == E[(1, p)] == 2 * p * (q - 1)
          and E[(q,)] == E[(1, q)] == 2 * q * (p - 1) and E[(1, p, q)] == 2 * (p * q - 1)
          and max(v for D, v in E.items() if D not in [(1,), (p, q)]) < 4 * (p - 1) * (q - 1))
    print(f"  (p,q)=({p},{q}) {E} ok={ok}")

print("(b) (a,b)=(2,2), q=3: set {1,3,p^2,3p^2,9p} vs maximum 62p^2-90p+40")
for p in [5, 7, 11]:
    n = 9 * p * p
    Dnear = tuple(sorted([1, 3, p * p, 3 * p * p, 9 * p]))
    e_near = energy(n, Dnear)
    best, arg = emax(n)
    conj = 62 * p * p - 90 * p + 40
    print(f"  p={p}: E_max={best} (formula {conj}) #maximisers={len(arg)} E(near)={e_near} gap={conj - e_near} (2(p-3)={2*(p-3)})")

print("(c) Theorem onem value for n = p q^m, m odd; and n = p^m q")
for p, q, m in [(5, 3, 1), (5, 3, 3), (3, 5, 3), (7, 3, 3), (3, 7, 1)]:
    n = p * q ** m
    best, arg = emax(n)
    val = Fr(n + (3 * p - 4) * d_closed(m, q), 2) - (p - 2) * delta_closed(m, q)
    anti = tuple(sorted(p ** i * q ** j for i in range(2) for j in range(m + 1) if (i + j) % 2 == 1))
    trunc = tuple(sorted(p ** i * q ** j for i in range(2) for j in range(m + 1) if (i + j) % 2 == 0 and p ** i * q ** j != n))
    print(f"  n={n}=({p})({q}^{m}): E_max={best} value={val} maximisers ok={sorted(arg) == sorted([anti, trunc])}")
for p, q, m in [(3, 5, 3), (5, 3, 3)]:   # n = p^m q
    n = p ** m * q
    best, arg = emax(n)
    val = Fr(n + (3 * q - 4) * d_closed(m, p), 2) - (q - 2) * delta_closed(m, p)
    print(f"  n={n}=({p}^{m})({q}): E_max={best} value={val}")

print("(d) anti-checkerboard energy = (n + d_a d_b)/2 - delta_a delta_b (equal parity)")
for (a, b) in [(2, 2), (1, 3), (3, 3), (2, 4)]:
    for p, q in [(3, 5), (5, 3), (5, 7)]:
        n = p ** a * q ** b
        if n > 20000: continue
        anti = [p ** i * q ** j for i in range(a + 1) for j in range(b + 1) if (i + j) % 2 == 1]
        e = energy(n, anti)
        val = Fr(n + d_closed(a, p) * d_closed(b, q), 2) - delta_closed(a, p) * delta_closed(b, q)
        print(f"  (a,b)=({a},{b}) (p,q)=({p},{q}) n={n}: E(anti)={e} value={val} ok={e == val}")
