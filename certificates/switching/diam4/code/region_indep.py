#!/usr/bin/env python3
"""Independent re-check of the region searches (second implementation, PROOF.md section 9.21).
For each tree of region(NT): compute an UPPER bound N_up on the number of non-even secular pairs WITHOUT factoring
R(x^2) over Q:  factor R(t) over Q (sympy, lower degree), and for each irreducible factor h(t) try to certify that
h(x^2) is irreducible over Q by exhibiting a prime p (p not dividing lc*disc) for which h(x^2) mod p is irreducible
(Rabin's test, own implementation below).  Certified factors are even orbits; the rest are counted in N_up.
N_ei is computed by testing even non-square integers t directly (R(t) == 0), without sympy.
A tree is 'cleared' if N_up < NT, or Row criterion (a) or (b) holds with N replaced by N_up (both are monotone).
Prints the trees that are NOT cleared; they must be a subset of the known exceptional trees (or have a
non-certifiable even orbit, reported separately)."""
import os, sys, itertools, math, sympy
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from row_lemmas import L_values
t = sympy.Symbol('t')
PRIMES = [p for p in range(3, 400) if sympy.isprime(p)]

# ---------- polynomial arithmetic over F_p (lists of ints, index = degree) ----------
def ptrim(a):
    while a and a[-1] == 0: a.pop()
    return a
def pmod(a, f, p):
    a = [c % p for c in a]; ptrim(a)
    df = len(f) - 1; inv = pow(f[-1], p - 2, p)
    while len(a) - 1 >= df:
        c = a[-1] * inv % p; sh = len(a) - 1 - df
        for i in range(len(f)): a[sh + i] = (a[sh + i] - c * f[i]) % p
        ptrim(a)
    return a
def pmul(a, b, f, p):
    if not a or not b: return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b): r[i + j] = (r[i + j] + x * y) % p
    return pmod(r, f, p)
def ppow_x(e, f, p):          # x^e mod f
    result = [1]; base = pmod([0, 1], f, p)
    while e:
        if e & 1: result = pmul(result, base, f, p)
        base = pmul(base, base, f, p); e >>= 1
    return result
def pgcd(a, b, p):
    a = [c % p for c in a]; b = [c % p for c in b]; ptrim(a); ptrim(b)
    while b:
        a, b = b, pmod(a, b, p)
    return a
def frob_iter(y, k, f, p):    # y^(p^k) mod f  (y a polynomial)
    for _ in range(k):
        # y^p mod f by square-and-multiply
        res = [1]; base = y[:]; e = p
        while e:
            if e & 1: res = pmul(res, base, f, p)
            base = pmul(base, base, f, p); e >>= 1
        y = res
    return y
def rabin_irreducible(fcoeffs, p):
    """fcoeffs: integer coefficients, index = degree; monic over F_p assumed after reduction"""
    f = [c % p for c in fcoeffs]; ptrim(f)
    d = len(f) - 1
    if d <= 0 or f[-1] == 0: return False
    inv = pow(f[-1], p - 2, p); f = [c * inv % p for c in f]
    x = [0, 1]
    xpd = frob_iter(pmod(x, f, p), d, f, p)
    diff = [(a - b) % p for a, b in itertools.zip_longest(xpd, pmod(x, f, p), fillvalue=0)]
    if ptrim(diff): return False
    for q in sympy.primefactors(d):
        y = frob_iter(pmod(x, f, p), d // q, f, p)
        diff = [(a - b) % p for a, b in itertools.zip_longest(y, [0, 1], fillvalue=0)]
        ptrim(diff)
        g = pgcd(f, diff, p) if diff else f
        if len(g) - 1 > 0: return False
    return True

def secular_int_coeffs(a):
    g = Counter(a); bs = sorted(g)
    E = sympy.Poly(1, t)
    for b in bs: E = E * sympy.Poly(t - b, t)
    S = sympy.Poly(0, t)
    for b in bs:
        term = sympy.Poly(g[b], t)
        for b2 in bs:
            if b2 != b: term = term * sympy.Poly(t - b2, t)
        S = S + term
    return E - S

def N_upper(a):
    R = secular_int_coeffs(a)
    nup = 0; uncert = []
    for h, m in sympy.factor_list(R.as_expr(), t)[1]:
        hp = sympy.Poly(h, t)
        coeffs = [int(c) for c in reversed(hp.all_coeffs())]      # index = degree in t
        hx2 = [0] * (2 * len(coeffs) - 1)
        for i, c in enumerate(coeffs): hx2[2 * i] = c                 # h(x^2)
        if len(coeffs) == 2 and coeffs[0] <= 0:
            v = -coeffs[0] // coeffs[1] if coeffs[1] else None
            if v is not None and v >= 0 and math.isqrt(v) ** 2 == v and v * coeffs[1] == -coeffs[0]:
                nup += 1; continue                                    # t = square: non-even (exact)
        disc = int(sympy.discriminant(sympy.Poly(sum(c * sympy.Symbol('x') ** i for i, c in enumerate(hx2)), sympy.Symbol('x'))))
        lc = hx2[-1]
        cert = False
        for p in PRIMES:
            if lc % p == 0 or disc % p == 0: continue
            if rabin_irreducible(hx2, p): cert = True; break
        if not cert: nup += 1; uncert.append(str(h))
    return nup, uncert

def N_ei_direct(a):
    g = Counter(a)
    top = max(g) + len(a) + 1
    cnt = 0
    for tv in range(2, top + 1, 2):
        if math.isqrt(tv) ** 2 == tv or tv in g: continue
        # F(tv) == 1 exactly?
        from fractions import Fraction
        F = sum(Fraction(g[b], tv - b) for b in g)
        if F == 1: cnt += 1
    return cnt

def criteria_up(a, N):
    g = Counter(a)
    for beta in g:
        if beta == 0: continue
        if len(L_values(beta, g[beta])) >= 2 * N + 1: return True
    k0 = g.get(0, 0)
    if k0 >= 1 and 2 * (k0 + 1) > 4 * N + N_ei_direct(a): return True
    return False

if __name__ == '__main__':
    NT, m, rr = map(int, sys.argv[1:4])
    maxb = 2 * NT + 1; kmax = {}
    for beta in range(2, maxb + 1):
        k = 0
        while True:
            kk = k + 1; size = kk * beta - 1 - (1 if (beta == 2 and kk == 2) else 0)
            if size <= 2 * NT: k = kk
            else: break
        kmax[beta] = k
    betas = sorted(kmax); idx = 0; count = 0; notcleared = []
    for ks in itertools.product(*[range(kmax[b] + 1) for b in betas]):
        if sum(ks) == 0: continue
        r_big = sum(1 for k in ks if k > 0)
        for k1 in range(0, 2 * NT + 2):
            r_nb = r_big + (1 if k1 > 0 else 0)
            k0max = (4 * NT + r_nb + 1) // 2 - 1
            for k0 in range(0, k0max + 1):
                idx += 1
                if (idx - 1) % m != rr: continue
                a = []
                for b, k in zip(betas, ks): a += [b] * k
                a += [1] * k1 + [0] * k0
                a = tuple(sorted(a, reverse=True)); count += 1
                nup, unc = N_upper(a)
                if nup < NT: continue
                if criteria_up(a, nup): continue
                notcleared.append((a, nup, unc)); print('NOT CLEARED', a, 'N_up=', nup, 'uncertified even-candidates:', unc, flush=True)
    print(f"INDEP NT={NT} shard={rr}/{m} trees={count} not_cleared={len(notcleared)}", flush=True)
