#!/usr/bin/env python3
"""Implementation A (Python, independent of swtrees.c): exhaustive exact check of the
switching conjecture for main eigenvalues on all trees with n vertices.

Independent choices (vs. implementation B = swtrees.c):
  * tree generation: canonical augmentation (add a leaf to every vertex of every tree
    on n-1 vertices, deduplicate by the AHU canonical string at the centre); B uses the
    Wright-Richmond-Odlyzko-McKay level-sequence generator;
  * characteristic polynomial: rooted recursion in x,
        phi(T_v) = x*prod_c phi(T_c) - sum_c phi(T_c - c)*prod_{c'!=c} phi(T_c'),
        phi(T_v - v) = prod_c phi(T_c),
    with Python integers; B uses matching-number DP;
  * number of distinct eigenvalues d = n - deg gcd(phi, phi') computed by sympy over ZZ;
    B uses a certified modular gcd;
  * certificate: EXACT rank over Q of the Krylov matrix [s, As, ..., A^{d-1}s] by
    fraction-free (Bareiss) elimination with Python integers; B uses rank mod 2^31-1.
    Candidate s are proposed by a floating-point pre-screen (numpy), but only the exact
    rank decides.
Lemma used (standard): rank [s, As, ..., A^{n-1}s] = #{distinct theta : P_theta s != 0},
so s is good iff that rank equals d.
Usage: python3 swtrees_A.py NMAX   (prints one line per n = 3..NMAX)
"""
import sys, itertools, time
import numpy as np
import sympy
sys.setrecursionlimit(10000)

def centres(adj):
    n = len(adj)
    if n <= 2: return list(range(n))
    deg = [len(a) for a in adj]
    leaves = [v for v in range(n) if deg[v] == 1]
    count = len(leaves)
    while count < n:
        new = []
        for v in leaves:
            for w in adj[v]:
                deg[w] -= 1
                if deg[w] == 1: new.append(w)
        count += len(new)
        leaves = new
    return leaves

def canon(adj, n):
    # AHU canonical string of a free tree, rooted at its centre (or central edge)
    def enc(v, p):
        return '(' + ''.join(sorted(enc(w, v) for w in adj[v] if w != p)) + ')'
    cs = centres(adj)
    if len(cs) == 1:
        return enc(cs[0], -1)
    a, b = cs
    return 'E' + ''.join(sorted([enc(a, b), enc(b, a)]))

def trees_upto(nmax):
    # yields (n, list of adjacency lists)
    cur = {canon([[1], [0]], 2): [[1], [0]]}
    for n in range(3, nmax + 1):
        new = {}
        for adj in cur.values():
            m = len(adj)
            for v in range(m):
                a2 = [list(x) for x in adj] + [[v]]
                a2[v].append(m)
                c = canon(a2, m + 1)
                if c not in new: new[c] = a2
        cur = new
        yield n, list(cur.values())

def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b): r[i + j] += x * y
    return r
def padd(a, b):
    if len(a) < len(b): a, b = b, a
    r = list(a)
    for i, y in enumerate(b): r[i] += y
    return r
def charpoly(adj, n):
    # coefficient lists, index = power of x
    order = [0]; par = {0: -1}
    for v in order:
        for w in adj[v]:
            if w not in par: par[w] = v; order.append(w)
    F = {}; G = {}   # F[v] = phi(T_v), G[v] = phi(T_v - v)
    for v in reversed(order):
        ch = [c for c in adj[v] if c != par[v]]
        prodF = [1]
        for c in ch: prodF = pmul(prodF, F[c])
        G[v] = prodF
        tot = pmul([0, 1], prodF)
        for c in ch:
            term = G[c]
            for c2 in ch:
                if c2 != c: term = pmul(term, F[c2])
            tot = padd(tot, [-t for t in term])
        F[v] = tot
    return F[0]

def exact_rank(rows):
    # Bareiss fraction-free elimination on integer rows; returns rank over Q
    M = [list(r) for r in rows]
    m = len(M); ncol = len(M[0]); rank = 0; prev = 1
    for col in range(ncol):
        piv = None
        for r in range(rank, m):
            if M[r][col] != 0: piv = r; break
        if piv is None: continue
        M[rank], M[piv] = M[piv], M[rank]
        p = M[rank][col]
        for r in range(rank + 1, m):
            for c in range(col + 1, ncol):
                M[r][c] = (M[r][c] * p - M[rank][c] * M[r][col]) // prev
            M[r][col] = 0
        prev = p; rank += 1
        if rank == m: break
    return rank

def krylov_rows(adj, s, d):
    rows = []; v = list(s)
    for _ in range(d):
        rows.append(v)
        v = [sum(v[w] for w in adj[i]) for i in range(len(adj))]
    return rows

def check_tree(adj, n):
    phi = charpoly(adj, n)
    x = sympy.Symbol('x')
    P = sympy.Poly(list(reversed(phi)), x, domain='ZZ')
    g = sympy.gcd(P, P.diff(x))
    d = n - g.degree()
    # floating pre-screen to rank candidate switchings
    A = np.zeros((n, n))
    for i in range(n):
        for j in adj[i]: A[i, j] = 1
    w, V = np.linalg.eigh(A)
    groups = []; cur = [0]
    for i in range(1, n):
        if abs(w[i] - w[cur[-1]]) < 1e-6: cur.append(i)
        else: groups.append(cur); cur = [i]
    groups.append(cur)
    def scores(S):
        C = np.asarray(S, float) @ V
        return np.min(np.stack([(C[:, g_] ** 2).sum(axis=1) for g_ in groups]), axis=0)
    def tiers():
        yield [[1] * n] + [[-1 if i == v else 1 for i in range(n)] for v in range(n)]
        yield [[-1 if i in (u, v) else 1 for i in range(n)] for u, v in itertools.combinations(range(n), 2)]
        yield [[-1 if i in t else 1 for i in range(n)] for t in itertools.combinations(range(n), 3)]
        rng = np.random.default_rng(12345)
        yield [list(r) for r in rng.choice([-1, 1], size=(4000, n))]
        yield [[1] + list(b) for b in itertools.product([1, -1], repeat=n - 1)]
    for S in tiers():
        sc = scores(S)
        order = np.argsort(-sc)
        for idx in order[:3]:
            if sc[idx] <= 1e-9: break
            s = [int(t) for t in S[idx]]
            if exact_rank(krylov_rows(adj, s, d)) == d:
                return True, d, s
    return False, d, None

if __name__ == '__main__':
    nmax = int(sys.argv[1]); t0 = time.time()
    for n, trees in trees_upto(nmax):
        ok = 0; bad = []
        for adj in trees:
            res, d, s = check_tree(adj, n)
            if res: ok += 1
            else: bad.append(adj)
        print(f"n={n} trees={len(trees)} certified_exact={ok} fail={len(bad)} time={time.time()-t0:.1f}s", flush=True)
        for b in bad[:5]: print('  FAIL', b, flush=True)
