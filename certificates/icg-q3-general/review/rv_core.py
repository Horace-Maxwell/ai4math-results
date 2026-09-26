"""Independent reviewer code (written from scratch; does not import the note's scripts).

Exact-arithmetic helpers for the Jiang-Yang weighted prime-power Ramanujan matrices.
"""
from fractions import Fraction as Fr
from math import gcd
import cmath


# ---------------------------------------------------------------- number theory
def factorize(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def mobius(n):
    f = factorize(n)
    if any(e > 1 for e in f.values()):
        return 0
    return -1 if len(f) % 2 else 1


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def euler_phi(n):
    return sum(1 for h in range(1, n + 1) if gcd(h, n) == 1)


def ramanujan(m, t):
    """c_m(t) exactly, by Kluyver/von Sterneck: sum_{d | gcd(m,t)} mu(m/d) d  (gcd(m,0)=m)."""
    g = gcd(m, t) if t != 0 else m
    return sum(mobius(m // d) * d for d in divisors(g))


def ramanujan_numeric(m, t):
    """c_m(t) by the defining exponential sum (float cross-check)."""
    s = sum(cmath.exp(2j * cmath.pi * h * t / m) for h in range(1, m + 1) if gcd(h, m) == 1)
    return s.real


# ---------------------------------------------------------------- matrices
def T_ram(m, x):
    """T_m(x) for an integer prime x, built from phi and Ramanujan sums (JY (2.2))."""
    return [[euler_phi(x ** (m - i)) * ramanujan(x ** (m - j), x ** i) for j in range(m + 1)]
            for i in range(m + 1)]


def T_gen(m, x):
    """T_m(x) for real/rational x: 'formal prime' version of (2.1)-(2.2)."""
    x = Fr(x)

    def ph(e):
        return Fr(1) if e == 0 else x ** (e - 1) * (x - 1)

    def cc(a, i):  # c_{x^a}(x^i)
        if a == 0:
            return Fr(1)
        if a <= i:
            return x ** (a - 1) * (x - 1)
        if a == i + 1:
            return -x ** (a - 1)
        return Fr(0)

    return [[ph(m - i) * cc(m - j, i) for j in range(m + 1)] for i in range(m + 1)]


def matvec(M, v):
    return [sum(a * b for a, b in zip(row, v)) for row in M]


def matmul(A, B):
    Bt = list(zip(*B))
    return [[sum(a * b for a, b in zip(row, col)) for col in Bt] for row in A]


def transpose(A):
    return [list(r) for r in zip(*A)]


def l1(v):
    return sum(abs(e) for e in v)


def l1mat(A):
    return sum(abs(e) for row in A for e in row)


def svec(m):
    return [(-1) ** i for i in range(m + 1)]


def d_formula(k, x):
    """JY (1.4)."""
    x = Fr(x)
    return (2 * k + 1) * x ** k + 4 * sum((-1) ** (k - j) * (j + 1) * x ** j for j in range(k))


def R(i, x):
    x = Fr(x)
    return sum((-1) ** (i - e) * x ** e for e in range(i + 1))


def delta_diag(k, x):
    """JY (3.3)-(3.4)."""
    x = Fr(x)
    d = [2 * x ** (k - i - 1) * (x - 1) * R(i, x) for i in range(k)]
    d.append((x ** k * (x - 1) + 2 * (-1) ** k) / (x + 1))
    return d


# ---------------------------------------------------------------- path / potential
def zpath(w, x):
    """Return dict z[k] for k=-1..m-1 with z_{m-1}=w_m, z_{k-1}=(z_k+(x-1)w_k)/x.
    Works for scalars or for lists (vector-valued rows)."""
    x = Fr(x)
    m = len(w) - 1
    z = {m - 1: w[m]}
    for k in range(m - 1, -1, -1):
        zk = z[k]
        if isinstance(zk, list):
            z[k - 1] = [(a + (x - 1) * b) / x for a, b in zip(zk, w[k])]
        else:
            z[k - 1] = (zk + (x - 1) * w[k]) / x
    return z


def mu_c(m, x):
    """mu[-1..m-1], c[0..m-1] of Lemma 2."""
    x = Fr(x)
    mu = {-1: Fr(1)}
    c = {}
    for k in range(m):
        c[k] = (x - 1) * (1 + mu[k - 1]) / x
        mu[k] = (x - 1 - mu[k - 1]) / x
    return mu, c
