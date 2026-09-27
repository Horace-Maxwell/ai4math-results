#!/usr/bin/env python3
"""PROOF.md section 9.22: the 5 trees left uncovered after session 2 (n <= 30), checked against the new
argument (Theorem 9.22.2 / refined criteria (a'), (b')), and explicit good switchings for the 3 trees that the
finite search leaves over.  Every family member is tested exactly (Bareiss rank over Q); the switching printed
is re-checked with the independent Galois-factor criterion."""
import os, sys, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'code'))
from collections import Counter
from ht2 import make_s, is_good, build
from row_lemmas import L_values, leaf_row_switch, bare_row_switch
from final_region import int_roots, issq, exact_pairs, L_of
import sympy
X = sympy.Symbol('x')

def galois_good(aa, s):
    adj, _ = build(aa); n = len(adj)
    A = sympy.zeros(n, n)
    for i in range(n):
        for j in adj[i]: A[i, j] = 1
    facs = [sympy.Poly(f, X) for f, m in sympy.factor_list(A.charpoly(X).as_expr())[1]]
    mu = sympy.Poly(1, X)
    for f in facs: mu = mu * f
    for f in facs:
        q = sympy.Poly(sympy.quo(mu.as_expr(), f.as_expr(), X), X).all_coeffs()
        v = [0] * n
        for c in q: v = [sum(v[w] for w in adj[i]) + int(c) * s[i] for i in range(n)]
        if all(z == 0 for z in v): return False
    return True

def sstr(s): return ''.join('+' if v > 0 else '-' for v in s)

FIVE = [(3, 1, 1, 1, 1, 0, 0, 0), (6, 3, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0), (8, 8, 1, 1, 1, 0, 0),
        (8, 5, 2, 2, 0, 0, 0, 0, 0), (6, 4, 3, 2, 1, 1, 1, 1)]
FINAL = [(2, 2), (2, 0, 0), (3,)]
for a in FIVE + FINAL:
    g = Counter(a); B = sorted(g); kk = dict(g); n = 1 + len(a) + sum(a)
    rts = int_roots(B, kk); NI, NII = exact_pairs(B, kk)
    Nei = sum(1 for v in rts if v % 2 == 0 and not issq(v)); k0 = g.get(0, 0); bs = max(a)
    fam = None
    for beta in sorted(B, reverse=True):
        if beta >= 1 and L_of(beta, g[beta]) >= 2 * NI + NII + 1: fam = ('leaf', beta); break
    if fam is None and k0 >= 1 and 2 * (k0 + 1) > 4 * NI + 2 * NII + Nei: fam = ('bare', None)
    print('T%s n=%d b*=%d B=%s N_I=%d N_II=%d N_ei=%d integer roots=%s' % (a, n, bs, B, NI, NII, Nei, rts))
    if fam:
        if fam[0] == 'leaf':
            beta = fam[1]
            mem = [('leaf-row beta=%d Lambda=%d eps=%+d' % (beta, Lam, e), leaf_row_switch(a, beta, Lam, e))
                   for Lam in L_values(beta, g[beta]) for e in (1, -1)]
            bound = 4 * NI + 2 * NII
            print("   criterion (a') at beta=%d: |L_beta| = %d >= 2N_I + N_II + 1 = %d" % (beta, L_of(beta, g[beta]), 2 * NI + NII + 1))
        else:
            mem = [('bare-row m=%d eps=%+d' % (m, e), bare_row_switch(a, m, e)) for m in range(k0 + 1) for e in (1, -1)]
            bound = 4 * NI + 2 * NII + Nei
            print("   criterion (b'): 2(k0+1) = %d > 4N_I + 2N_II + N_ei = %d" % (2 * (k0 + 1), bound))
        good = []
        for name, (aa, sc, sg, mu) in mem:
            s, adj = make_s(aa, sc, sg, mu)
            if is_good(aa, s, adj): good.append((name, aa, s))
        print('   family size %d, bad %d (bound %d)' % (len(mem), len(mem) - len(good), bound))
        name, aa, s = good[0]
        print('   good member: %s  s=%s  Galois check: %s' % (name, sstr(s), galois_good(aa, s)))
    else:
        aa = tuple(sorted(a)); adj, leaves = build(aa); nn = len(adj); found = None
        for bits in itertools.product((1, -1), repeat=nn - 1):
            s = [1] + list(bits)
            if is_good(aa, s, adj): found = s; break
        print("   not covered by (a')/(b'); N = %d; explicit good switching (first found, s_c=+1): s=%s  Galois check: %s"
              % (NI + NII, sstr(found), galois_good(aa, found)))
        print('   vertex order: centre, branches in nondecreasing size %s, then leaves branch by branch' % (aa,))
