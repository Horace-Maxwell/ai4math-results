#!/usr/bin/env python3
"""Task 2: independent exact check of Lemma S (spectrum of T(a)) and Lemma M (reduced form) on random trees.

(1) charpoly by generic tree recursion  ==  R(x^2) * prod_{b>=1}(x^2-b)^{k_b-1} * x^{m0}   (exact polynomial identity)
(2) d (from charpoly, exact)  ==  2r + 2#{b>=1: k_b>=2} + [m0>0]
(3) eigenvectors: secular vector satisfies A x = theta x modulo R(theta^2) (exact, sympy, rational functions);
    leaf-group vectors and kernel vectors satisfy A x = theta x exactly; their dimensions add up to n.
(4) Lemma M: for random s, for each irreducible factor f of R(x^2):  s.x(theta) = 0 (x secular eigenvector)
    <=>  G(theta) := s_c + sum_i (sigma_i theta + lambda_i)/(t - a_i) = 0  <=>  reduced form sum_b (A_b+S_b theta)/(t-b) = 0,
    all tested in Q[x]/(f); and the reduced-form prediction of goodness == exact Krylov Q-rank goodness.
"""
import sys, random
from collections import Counter
import sympy
from rv_common import tree_adj, charpoly_tree, distinct_eig_count, lemmaS_prediction, krylov_int, rank_Q, X

def check_tree(a, rng, nsw=4):
    a = sorted(a, reverse=True)
    adj = tree_adj(a); n = len(adj); k = len(a)
    phi = charpoly_tree(adj)
    pphi = sympy.Poly(list(reversed(phi)), X, domain='ZZ')
    pred, dS, m0 = lemmaS_prediction(a)
    ok1 = (pphi == pred)
    d = distinct_eig_count(phi)
    ok2 = (d == dS)
    # (3) eigenvectors
    kk = Counter(a); B = sorted(kk)
    th = X; t = X**2
    # leaves of branch i
    leaves = []; nxt = 1 + k
    for ai in a:
        leaves.append(list(range(nxt, nxt + ai))); nxt += ai
    def Ax(vec):
        return [sum(vec[u] for u in adj[i]) for i in range(n)]
    # secular vector with symbolic theta; residual must vanish mod R(theta^2)
    xs = [sympy.Integer(0)] * n
    xs[0] = sympy.Integer(1)
    for i, ai in enumerate(a):
        xs[1 + i] = th / (t - ai)
        for l in leaves[i]: xs[l] = 1 / (t - ai)
    Rt = sympy.expand(sympy.prod([X**2 - b for b in B]) - sum(kk[b] * sympy.prod([X**2 - c for c in B if c != b]) for b in B))
    ok3 = True
    Avx = Ax(xs)
    den = sympy.prod([X**2 - b for b in B])
    for i in range(n):
        res = sympy.cancel((Avx[i] - th * xs[i]) * den)
        num = sympy.Poly(sympy.numer(sympy.together(res)), X)
        dd = sympy.Poly(sympy.denom(sympy.together(res)), X)
        if not num.is_zero:
            rem = num.rem(sympy.Poly(Rt, X))
            if not rem.is_zero: ok3 = False
    # leaf-group vectors: theta = +-sqrt(b); check with explicit alpha (e_1 - e_j) in group b: need theta symbolic with theta^2=b
    dimsum = 2 * len(B)
    for b in B:
        if b >= 1 and kk[b] >= 2:
            idx = [i for i in range(k) if a[i] == b]
            for j in idx[1:]:
                vec = [sympy.Integer(0)] * n
                vec[1 + idx[0]] = sympy.Integer(1); vec[1 + j] = sympy.Integer(-1)
                for l in leaves[idx[0]]: vec[l] = 1 / th
                for l in leaves[j]: vec[l] = -1 / th
                Av = Ax(vec)
                for i in range(n):
                    res = sympy.together(Av[i] - th * vec[i])
                    num = sympy.Poly(sympy.numer(res), X)
                    if not num.is_zero and not num.rem(sympy.Poly(X**2 - b, X)).is_zero: ok3 = False
            dimsum += 2 * (kk[b] - 1)
    # kernel: dimension by exact rank of A
    import sympy as sp
    Am = sp.zeros(n, n)
    for i in range(n):
        for u in adj[i]: Am[i, u] = 1
    ker = n - Am.rank()
    ok3 = ok3 and (ker == m0) and (dimsum + ker == n)
    # (4) Lemma M on random switchings
    ok4 = True
    fac = sympy.factor_list(sympy.Poly(Rt, X))[1]
    for _ in range(nsw):
        s = [rng.choice((1, -1)) for _ in range(n)]
        sc = s[0]; sig = s[1:1 + k]; lam = [sum(s[l] for l in leaves[i]) for i in range(k)]
        G = sc + sum((sig[i] * th + lam[i]) / (t - a[i]) for i in range(k))
        Ab = {b: sum(sc + lam[i] for i in range(k) if a[i] == b) for b in B}
        Sb = {b: sum(sig[i] for i in range(k) if a[i] == b) for b in B}
        Gred = sum((Ab[b] + Sb[b] * th) / (t - b) for b in B)
        sx = sum(s[i] * xs[i] for i in range(n))
        pred_good = True
        for f, _m in fac:
            fp = sympy.Poly(f, X)
            vals = []
            for expr in (G, Gred, sx):
                e = sympy.together(expr)
                num = sympy.Poly(sympy.numer(e), X); de = sympy.Poly(sympy.denom(e), X)
                # denominator is nonzero at roots of f (no pole is a secular root); numerator mod f
                assert not de.rem(fp).is_zero or de.gcd(fp).degree() == 0
                vals.append(num.rem(fp).is_zero)
            if not (vals[0] == vals[1] == vals[2]): ok4 = False
            if vals[0]: pred_good = False
        # leaf-group condition (L) and kernel condition (Z)
        for b in B:
            if b >= 1 and kk[b] >= 2:
                idx = [i for i in range(k) if a[i] == b]
                # (sigma_i + lambda_i/theta) constant over idx, for theta = +-sqrt(b)
                for sgn in (1, -1):
                    th0 = sgn * sympy.sqrt(b)
                    vals = set(sympy.nsimplify(sig[i] + lam[i] / th0) for i in idx)
                    if len(vals) == 1: pred_good = False
        k0 = kk.get(0, 0)
        if m0 > 0:
            if k0 >= 1:
                nonconst = any(len(set(s[l] for l in leaves[i])) > 1 for i in range(k) if a[i] >= 2) or \
                           len(set(sig[i] for i in range(k) if a[i] == 0)) > 1
            else:
                nonconst = any(len(set(s[l] for l in leaves[i])) > 1 for i in range(k) if a[i] >= 2) or \
                           sc != sum(s[leaves[i][0]] for i in range(k))
            if not nonconst: pred_good = False
        exact_good = (rank_Q(krylov_int(adj, s, d)) == d)
        if exact_good != pred_good: ok4 = False
    return ok1, ok2, ok3, ok4

if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    ntrees = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    rng = random.Random(seed)
    bad = 0
    cases = [(2, 2), (2, 0, 0), (3,), (3, 1, 1, 1, 1, 0, 0, 0), (12, 12, 8, 0, 0, 0, 0, 0, 0), (1, 1, 1), (0, 0, 0, 0),
             (1, 0, 0), (1, 1, 0, 0), (2, 2, 0, 0, 0), (6, 3, 2) + (0,) * 9, (8, 5, 2, 2, 0, 0, 0, 0, 0)]
    while len(cases) < ntrees:
        k = rng.randint(1, 7)
        a = tuple(rng.choice([0, 0, 1, 1, 2, 2, 3, 4, 5, 6, 8]) for _ in range(k))
        if 1 + k + sum(a) >= 3 and 1 + k + sum(a) <= 34: cases.append(a)
    for a in cases:
        r = check_tree(a, rng)
        flag = 'OK' if all(r) else 'FAIL'
        if not all(r): bad += 1
        print(flag, sorted(a, reverse=True), 'charpoly=%s d=%s eigvec=%s lemmaM=%s' % r, flush=True)
    print('SUMMARY trees=%d failures=%d' % (len(cases), bad))
