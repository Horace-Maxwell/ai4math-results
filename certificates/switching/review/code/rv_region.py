#!/usr/bin/env python3
"""Task 4 (referee, independent): re-derive the finite set of Lemma 9.22.3 and the trees failing (a') and (b').

Enumeration: itertools.product over multiplicity vectors (k_0..k_{b*}) with crude global caps, then an exact
per-B filter derived by the referee:
   a tree failing (a') at every beta>=1 in B and failing (b') must satisfy, with
   U_I = min(r, 1 + #{q>=1 : q^2 <= b*-1, q^2 not in B}),
   Mx = max{2 NI + NII : 0<=NI<=U_I, NI + 2 NII <= r},  K0 = max{4NI + 2NII + Nei : NI<=U_I, NI+2NII+Nei <= r}:
      L(beta, k_beta) <= Mx for all beta>=1 in B;   k_0 = 0 or 2(k_0+1) <= K0.
Exact invariants for EVERY tree in the set (not only cheap-test survivors), certified orbit by orbit:
   N_I  = #(non-even linear factor pairs x-q, x+q),  N_II = #(non-even pairs of degree >= 2),
   N_ei = #(even factors x^2 - c with c an even integer)  [irreducible => c non-square].
integer roots by exact Fraction evaluation of F(t)=1; orbits = sympy factor_list of R(t) (deg <= 13), each factor certified irreducible by the referee's own Rabin test mod p; even orbit certified by a simple root c of h mod p with c a QNR (p-adic argument); non-even certified by explicit g with g(x)g(-x) = +-h(x^2).
Output: the set (one tree per line), the survivors of (a')/(b'), and summary counts.
"""
import sys, math, itertools, subprocess, os, tempfile
from fractions import Fraction
from collections import Counter

def L(beta, k):
    if beta == 1:
        return 2 if k == 1 else k - 1
    return k * beta - 1 - (1 if (beta == 2 and k == 2) else 0)

def bounds(B, bstar):
    r = len(B)
    sq = sum(1 for q in range(1, bstar + 1) if q * q <= bstar - 1 and q * q not in B)
    UI = min(r, 1 + sq)
    Mx = max(2 * NI + NII for NI in range(0, UI + 1) for NII in range(0, r + 1) if NI + 2 * NII <= r)
    K0 = max(4 * NI + 2 * NII + Nei for NI in range(0, UI + 1) for NII in range(0, r + 1)
             for Nei in range(0, r + 1) if NI + 2 * NII + Nei <= r)
    return UI, Mx, K0

def enumerate_region():
    out = []
    for bstar in range(2, 13):
        # crude caps: global maxima of Mx, K0 over all B for this b*
        allB = [tuple(sorted(set(c) | {bstar})) for m in range(bstar + 1) for c in itertools.combinations(range(bstar), m)]
        gMx = max(bounds(B, bstar)[1] for B in allB)
        gK0 = max(bounds(B, bstar)[2] for B in allB)
        ranges = []
        for b in range(0, bstar + 1):
            if b == 0:
                cap = max(k for k in range(0, 100) if k == 0 or 2 * (k + 1) <= gK0)
            else:
                cap = max(k for k in range(1, 200) if L(b, k) <= gMx)
            lo = 1 if b == bstar else 0
            ranges.append(range(lo, cap + 1))
        cache = {}
        for ks in itertools.product(*ranges):
            B = tuple(b for b in range(bstar + 1) if ks[b] > 0)
            if B not in cache: cache[B] = bounds(B, bstar)
            UI, Mx, K0 = cache[B]
            ok = True
            for b in B:
                if b >= 1 and L(b, ks[b]) > Mx: ok = False; break
            if not ok: continue
            if ks[0] > 0 and 2 * (ks[0] + 1) > K0: continue
            a = tuple(b for b in range(bstar, -1, -1) for _ in range(ks[b]))
            out.append(a)
    return out

def int_secular_roots(a):
    kk = Counter(a); B = sorted(kk); K = len(a)
    roots = []
    for t in range(max(1, B[0] + 1), B[-1] + K + 1):
        if t in kk: continue
        if sum(Fraction(kk[b], t - b) for b in B) == 1: roots.append(t)
    return roots


import sympy
T_, X_ = sympy.symbols('t x')

def R_poly(a):
    kk = Counter(a); B = sorted(kk)
    R = sympy.prod([T_ - b for b in B]) - sum(kk[b] * sympy.prod([T_ - c for c in B if c != b]) for b in B)
    return sympy.Poly(sympy.expand(R), T_)

# ---- polynomial arithmetic over F_p (lists low->high), referee's own code ----
def _trim(a):
    while a and a[-1] == 0: a.pop()
    return a
def _mod(a, h, p):
    a = [x % p for x in a]; _trim(a)
    m = len(h) - 1; inv = pow(h[-1], p - 2, p)
    while len(a) - 1 >= m and a:
        c = a[-1] * inv % p; sh = len(a) - 1 - m
        for i in range(m + 1): a[sh + i] = (a[sh + i] - c * h[i]) % p
        _trim(a)
    return a
def _mul(a, b, h, p):
    if not a or not b: return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b): r[i + j] += x * y
    return _mod(r, h, p)
def _pow(base, e, h, p):
    res = [1]; b = _mod(list(base), h, p)
    while e:
        if e & 1: res = _mul(res, b, h, p)
        b = _mul(b, b, h, p); e >>= 1
    return res
def _gcd(a, b, p):
    a = _trim([x % p for x in a]); b = _trim([x % p for x in b])
    while b:
        a, b = b, _mod(a, b, p)
    return a
def _sub(a, b, p):
    m = max(len(a), len(b)); r = [0] * m
    for i, x in enumerate(a): r[i] += x
    for i, x in enumerate(b): r[i] -= x
    return _trim([x % p for x in r])
def _primes(lo, hi):
    return [q for q in range(lo, hi) if q > 1 and all(q % d for d in range(2, int(q ** 0.5) + 1))]
PR = _primes(3, 4000)

def rabin_irreducible_mod_p(h, p):
    """h: integer coeff list low->high, monic, degree m. Rabin's test over F_p."""
    m = len(h) - 1
    hp = [x % p for x in h]
    y = [0, 1]
    # y^(p^m) == y mod h
    z = y
    for _ in range(m): z = _pow(z, p, hp, p)
    if _sub(z, y, p): return False
    for q in set(d for d in range(2, m + 1) if m % d == 0 and all(d % e for e in range(2, d))):
        z = y
        for _ in range(m // q): z = _pow(z, p, hp, p)
        g = _gcd(hp, _sub(z, y, p), p)
        if len(g) - 1 != 0: return False
    return True

def certify_irreducible(h):
    for p in PR[:300]:
        if rabin_irreducible_mod_p(h, p): return p
    return None

def certify_even(h):
    """orbit of h is even (h(x^2) irreducible) if some odd prime p has a simple root c of h mod p with c a QNR."""
    m = len(h) - 1
    dh = [i * h[i] for i in range(1, m + 1)]
    for p in PR:
        for c in range(1, p):
            v = 0
            for co in reversed(h): v = (v * c + co) % p
            if v == 0:
                dv = 0
                for co in reversed(dh): dv = (dv * c + co) % p
                if dv != 0 and pow(c, (p - 1) // 2, p) == p - 1:
                    return (p, c)
    return None

def certify_noneven(hs):
    """return g with g(x) g(-x) = +-h(x^2) verified exactly, else None"""
    H = sympy.Poly(hs.as_expr().subs(T_, X_ ** 2), X_)
    for f, e in sympy.factor_list(H)[1]:
        g = sympy.Poly(f, X_)
        if g.degree() * 2 == H.degree():
            gm = sympy.Poly(g.as_expr().subs(X_, -X_), X_)
            prod = g * gm
            if prod == H or prod == -H:
                return g
    return None

STRICT = True

def classify(a):
    """exact (N_I, N_II, N_ei) with certificates; returns (NI, NII_low, NII_up, Nei, notes)"""
    Rp = R_poly(a)
    roots = int_secular_roots(a)
    NI = sum(1 for t in roots if math.isqrt(t) ** 2 == t)
    Nei = sum(1 for t in roots if t % 2 == 0 and math.isqrt(t) ** 2 != t)
    lo = up = 0; notes = []
    deg_lin = 0
    for f, e in sympy.factor_list(Rp)[1]:
        fp = sympy.Poly(f, T_)
        if fp.LC() < 0: fp = -fp
        assert e == 1
        if fp.degree() == 1:
            deg_lin += 1
            assert -fp.all_coeffs()[1] in roots
            continue
        h = [int(c) for c in reversed(fp.all_coeffs())]
        assert h[-1] == 1
        irr = certify_irreducible(h)
        if irr is None:
            if STRICT:
                up += fp.degree() // 2; notes.append(('irr-uncert', fp.degree())); continue
            notes.append(('irr-by-sympy-only', fp.degree()))   # sympy factor_list over Z is exact; no m-cycle mod p
        ev = certify_even(h)
        if ev is not None:
            continue
        g = certify_noneven(fp)
        if g is not None:
            lo += 1; up += 1
        else:
            up += 1; notes.append(('even-uncert', fp.degree()))
    assert deg_lin == len(roots), (a, roots, deg_lin)
    return NI, lo, up, Nei, notes

def criteria(a, NI, NII, Nei):
    kk = Counter(a)
    oka = any(L(b, kk[b]) >= 2 * NI + NII + 1 for b in kk if b >= 1)
    k0 = kk.get(0, 0)
    okb = k0 >= 1 and 2 * (k0 + 1) > 4 * NI + 2 * NII + Nei
    return oka, okb

if __name__ == '__main__':
    outdir = sys.argv[1] if len(sys.argv) > 1 else '.'
    region = enumerate_region()
    print('REGION size', len(region), 'max n', max(1 + len(a) + sum(a) for a in region), flush=True)
    with open(os.path.join(outdir, 'rv_region_list.txt'), 'w') as fh:
        for a in region: fh.write(' '.join(map(str, a)) + '\n')
    surv = []; mism = 0; viol = 0; uncert = []
    Ndist = Counter()
    for idx, a in enumerate(region):
        NI, NIIlo, NIIup, Nei, notes = classify(a)
        if NIIlo != NIIup or notes: uncert.append((a, NI, NIIlo, NIIup, Nei, notes))
        NII = NIIup
        kk = Counter(a); B = sorted(kk); r = len(B); bstar = B[-1]
        sq = sum(1 for q in range(1, bstar + 1) if q * q <= bstar - 1 and q * q not in B)
        if not (NI <= sq + 1 and NI + 2 * NIIlo + Nei <= r): viol += 1; print('BOUND-VIOLATION', a, NI, NIIlo, Nei, r, sq)
        Ndist[NI + NIIup] += 1
        oka, okb = criteria(a, NI, NII, Nei)
        if not (oka or okb):
            surv.append((a, NI, NII, Nei))
    print('uncertified orbit classifications:', len(uncert))
    for u in uncert[:50]: print('UNCERT', u)
    print('a-priori bound violations:', viol)
    print('N distribution over the region:', dict(sorted(Ndist.items())))
    print('SURVIVORS failing (a\') and (b\') with exact N_I, N_II, N_ei:', len(surv))
    for s in surv: print('SURVIVOR', s[0], 'n=%d' % (1 + len(s[0]) + sum(s[0])), 'N_I=%d N_II=%d N_ei=%d' % s[1:])
