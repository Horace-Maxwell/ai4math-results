#!/usr/bin/env python3
"""Census of non-even secular pairs for T(a), n in [N0, N1], shard r of m.
For each tree with >= 2 non-even pairs, print a, the pairs (as factor g(x) with g(-x) its partner), and group data."""
import os, sys, sympy
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ht2 import all_ht2
x, t = sympy.symbols('x t')
def secular_poly(a):
    g = Counter(a); bs = sorted(g)
    E = sympy.Integer(1)
    for b in bs: E *= (t - b)
    S = 0
    for b in bs:
        term = sympy.Integer(g[b])
        for b2 in bs:
            if b2 != b: term *= (t - b2)
        S += term
    return sympy.Poly(sympy.expand(E - S), t)
def noneven_pairs(a):
    R = secular_poly(a)
    Rx = sympy.Poly(R.as_expr().subs(t, x**2), x)
    out = []
    for f, m in sympy.factor_list(Rx.as_expr())[1]:
        pf = sympy.Poly(f, x); pm = sympy.Poly(f.subs(x, -x), x)
        if not (pm == pf or pm == -pf):
            lc = pf.LC()
            # keep one representative per pair: the factor whose second coefficient (sum of roots sign) is >= 0 ... canonical
            out.append(pf)
    reps = []
    seen = set()
    for pf in out:
        key = tuple(pf.monic().all_coeffs())
        partner = tuple(sympy.Poly(pf.as_expr().subs(x, -x), x).monic().all_coeffs())
        if partner in seen: continue
        seen.add(key); reps.append(pf)
    return reps
if __name__ == '__main__':
    N0, N1, m, r = map(int, sys.argv[1:5])
    for n in range(N0, N1 + 1):
        dist = Counter(); idx = 0
        for a in all_ht2(n):
            idx += 1
            if (idx - 1) % m != r: continue
            ps = noneven_pairs(a)
            dist[len(ps)] += 1
            if len(ps) >= 2:
                print('MULTI', n, a, [str(p.as_expr()) for p in ps], flush=True)
        print(f"n={n} shard={r}/{m} dist={dict(sorted(dist.items()))}", flush=True)
