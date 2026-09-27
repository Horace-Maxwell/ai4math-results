# The 5 trees of diameter <= 4 with n <= 30 that were not covered by the session-2 theorems: check them against
# the Row Lemmas (section 9.15) and give explicit good switchings, verified twice (Bareiss rank over Q and the
# independent Galois-factor criterion of crosscheck_galois.py).
import os, sys, itertools
sys.path.insert(0, '.'); sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'code'))
from collections import Counter
from ht2 import make_s, is_good, build
from row_lemmas import criteria, L_values, leaf_row_switch, bare_row_switch
from crosscheck_galois import check as galois_check
FIVE = [(3,1,1,1,1,0,0,0), (6,3,2,0,0,0,0,0,0,0,0,0), (8,8,1,1,1,0,0), (8,5,2,2,0,0,0,0,0), (6,4,3,2,1,1,1,1)]
def galois_good(aa, s):
    adj, _ = build(aa); n = len(adj)
    edges = sorted((min(i, j), max(i, j)) for i in range(n) for j in adj[i] if i < j)
    # reuse check(): it enumerates U with |U| <= kmax; instead test the single s directly
    import sympy
    x = sympy.Symbol('x')
    A = sympy.zeros(n, n)
    for i, j in edges: A[i, j] = A[j, i] = 1
    facs = [sympy.Poly(f, x) for f, m in sympy.factor_list(A.charpoly(x).as_expr())[1]]
    mu = sympy.Poly(1, x)
    for f in facs: mu = mu * f
    for f in facs:
        q = sympy.Poly(sympy.quo(mu.as_expr(), f.as_expr(), x), x).all_coeffs()
        v = [0] * n
        for c in q: v = [sum(v[w] for w in adj[i]) + int(c) * s[i] for i in range(n)]
        if all(z == 0 for z in v): return False
    return True
for a in FIVE:
    g = Counter(a); c = criteria(a)
    print('T', a, 'n =', 1 + len(a) + sum(a), 'N =', c['N'], 'N_ei =', c['Nei'], 'criterion (a):', c['a'], '(b):', c['b'])
    fam = []
    if c['a']:
        beta = c['a'][0]
        for Lam in L_values(beta, g[beta]):
            for eps in (1, -1): fam.append(('leaf-row beta=%d Lambda=%d eps=%d' % (beta, Lam, eps), leaf_row_switch(a, beta, Lam, eps)))
    elif c['b']:
        for m in range(g[0] + 1):
            for eps in (1, -1): fam.append(('bare-row m=%d eps=%d' % (m, eps), bare_row_switch(a, m, eps)))
    if fam:
        good = []
        for name, (aa, sc, sg, mu) in fam:
            s, adj = make_s(aa, sc, sg, mu)
            if is_good(aa, s, adj): good.append((name, s))
        print('   family size', len(fam), ' bad', len(fam) - len(good), ' (bound 4N =', 4 * c['N'], ')')
        name, s = good[0]
        print('   first good:', name, ' s =', ''.join('+' if v > 0 else '-' for v in s), ' Galois-criterion check:', galois_good(tuple(sorted(a)), s))
    else:
        # exceptional: search explicit good switching with s_c=+1, sigma=+1, then any
        aa = tuple(sorted(a)); adj, leaves = build(aa); n = len(adj)
        found = None
        for sc in (1, -1):
            for mus in itertools.product(*[range(b + 1) for b in aa]):
                sg = [1] * len(aa)
                s, adj2 = make_s(aa, sc, sg, list(mus))
                if is_good(aa, s, adj2): found = s; break
            if found: break
        print('   EXCEPTIONAL: explicit good switching s =', ''.join('+' if v > 0 else '-' for v in found),
              ' (vertex order: centre, branches in nondecreasing size, then leaves branch by branch); Galois check:', galois_good(aa, found))
