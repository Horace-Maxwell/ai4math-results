#!/usr/bin/env python3
"""Row Lemma criterion (PROOF.md section 9.15) for trees T(a) with N >= 2 non-even secular pairs.
For beta in B, beta >= 1: L = set of realizable leaf-sum totals of group beta:
   beta >= 2: |L| = k*beta - 1, minus 1 if beta == 2 and k == 2 (the value 0 cannot keep both (L) and a non-constant branch);
   beta == 1: |L| = k - 1 if k >= 2 (variation), = 2 if k == 1; usable only if some other value b >= 2 exists ((Z) source).
A pair (theta, -theta) is 'special' for beta if theta*(theta^2 - beta) is an integer m with |m| <= |L| - 1.
Criterion: |L| > N + (#special pairs).  Prints trees failing the criterion for every beta."""
import os, sys, sympy
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from noneven_census import noneven_pairs
x = sympy.Symbol('x')
def Lsize(beta, k, g):
    if beta >= 2:
        return k * beta - 1 - (1 if (beta == 2 and k == 2) else 0)
    if beta == 1:
        if not any(b >= 2 for b in g): return 0
        return (k - 1) if k >= 2 else 2
    return 0
def special(pair_poly, beta, Lsz):
    g = pair_poly.monic()
    r = sympy.rem(sympy.Poly(x**3 - beta * x, x), g)      # theta^3 - beta*theta reduced mod minimal polynomial
    if r.degree() <= 0:
        m = r.as_expr()
        if m.is_integer and abs(int(m)) <= Lsz - 1: return True
    return False
def covered(a):
    g = Counter(a); pairs = noneven_pairs(a); N = len(pairs)
    best = None
    for beta in sorted(g, reverse=True):
        if beta == 0: continue
        Lsz = Lsize(beta, g[beta], g)
        if Lsz <= 0: continue
        ns = sum(1 for p in pairs if special(p, beta, Lsz))
        if Lsz > N + ns: return True, (beta, Lsz, N, ns)
        best = best or (beta, Lsz, N, ns)
    return False, best
if __name__ == '__main__':
    import re, ast, glob
    trees = []
    for f in sys.argv[1:]:
        for line in open(f):
            if line.startswith('MULTI'):
                parts = line.split(' ', 2)
                n = int(parts[1]); a = ast.literal_eval(parts[2][:parts[2].index(')') + 1])
                trees.append((n, a))
    trees.sort()
    unc = []
    for n, a in trees:
        ok, info = covered(a)
        print(n, a, 'COVERED' if ok else 'not covered', info, flush=True)
        if not ok: unc.append((n, a))
    print('uncovered:', len(unc), unc)
