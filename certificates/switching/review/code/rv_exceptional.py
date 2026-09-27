#!/usr/bin/env python3
"""Referee: the three leftover trees of Lemma 9.22.3, exhaustively (all 2^n switchings, exact Q-rank),
plus the switchings stated in PROOF.md §9.22 (vertex order: centre, branch vertices in nondecreasing size,
then leaves branch by branch) and an eigenvalue-by-eigenvalue projection check with sympy."""
import itertools, sympy
from rv_common import tree_adj, charpoly_tree, distinct_eig_count, krylov_int, rank_Q
cases = {'T(2,2)': ((2, 2), '+++++--'), 'D(2,2)=T(0,0,2)': ((0, 0, 2), '+++-+-'), 'K14=T(3)': ((3,), '+++--')}
for name, (a, sstr) in cases.items():
    adj = tree_adj(a); n = len(adj); phi = charpoly_tree(adj); d = distinct_eig_count(phi)
    good = [s for s in itertools.product((1, -1), repeat=n) if rank_Q(krylov_int(adj, list(s), d)) == d]
    s = [1 if c == '+' else -1 for c in sstr]
    ok = rank_Q(krylov_int(adj, s, d)) == d
    # projection check with exact eigenspaces
    A = sympy.zeros(n, n)
    for i in range(n):
        for u in adj[i]: A[i, u] = 1
    proj_ok = True; eigs = []
    for lam, mult, vecs in A.eigenvects():
        sv = sympy.Matrix(s)
        nz = any(sympy.simplify((sv.T * v)[0]) != 0 for v in vecs)
        eigs.append((lam, mult, nz)); proj_ok &= nz
    print(name, 'n=%d d=%d charpoly=%s' % (n, d, sympy.factor(sympy.Poly(list(reversed(phi)), sympy.Symbol('x')).as_expr())),
          '#good=%d/%d' % (len(good), 2 ** n), 'stated s=%s good(Krylov)=%s good(eigenspaces)=%s' % (sstr, ok, proj_ok), eigs)
