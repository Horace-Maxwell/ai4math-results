#!/usr/bin/env python3
"""Referee's independent toolkit (review of PROOF.md Thm 9.22).  Written from scratch; shares no code with diam4/code.

Tree T(a): vertex 0 = centre c, vertices 1..k = branch vertices v_i (in the order of the tuple a),
then the leaves of v_1, v_2, ... in order.

Certificates used:
  * charpoly(A) by the generic tree recursion (matching polynomial) -- independent of Lemma S;
  * d = number of distinct eigenvalues = deg phi - deg gcd(phi, phi')  (A symmetric => minpoly = rad(phi));
  * s is good  <=>  rank_Q [s, As, ..., A^{d-1}s] = d.  Certificate: rank over F_p equals d
    (rank_Fp <= rank_Q <= d always), checked for two primes; exact Q-rank (fraction-free Bareiss) available.
"""
import random
from math import gcd
import sympy

P1 = 2147483647          # 2^31 - 1
P2 = 2147483629          # another prime < 2^31

def tree_adj(a):
    a = list(a)
    k = len(a)
    n = 1 + k + sum(a)
    adj = [[] for _ in range(n)]
    nxt = 1 + k
    for i, ai in enumerate(a):
        v = 1 + i
        adj[0].append(v); adj[v].append(0)
        for _ in range(ai):
            adj[v].append(nxt); adj[nxt].append(v); nxt += 1
    assert nxt == n
    return adj

# ---------- integer polynomial helpers (coefficient lists, lowest degree first) ----------
def padd(p, q):
    m = max(len(p), len(q)); r = [0] * m
    for i, c in enumerate(p): r[i] += c
    for i, c in enumerate(q): r[i] += c
    while len(r) > 1 and r[-1] == 0: r.pop()
    return r

def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, c in enumerate(p):
        if c:
            for j, e in enumerate(q):
                if e: r[i + j] += c * e
    return r

def pneg(p): return [-c for c in p]

def charpoly_tree(adj, root=0):
    """phi(T) = matching polynomial.  For rooted subtree at v:  P_v = x*Q_v - sum_u Q_u * prod_{w != u} P_w,
    Q_v = prod_children P_u  (Q_u = charpoly of subtree(u) minus u)."""
    n = len(adj)
    parent = [-1] * n; order = []; seen = [False] * n
    stack = [root]; seen[root] = True
    while stack:
        v = stack.pop(); order.append(v)
        for u in adj[v]:
            if not seen[u]: seen[u] = True; parent[u] = v; stack.append(u)
    P = [None] * n; Q = [None] * n
    for v in reversed(order):
        ch = [u for u in adj[v] if u != parent[v]]
        q = [1]
        for u in ch: q = pmul(q, P[u])
        Q[v] = q
        s = [0]
        for u in ch:
            t = Q[u]
            for w in ch:
                if w != u: t = pmul(t, P[w])
            s = padd(s, t)
        P[v] = padd(pmul([0, 1], q), pneg(s))
    return P[root]

X = sympy.Symbol('x')

def distinct_eig_count(phi):
    """d = deg phi - deg gcd(phi, phi') (exact, over Z)."""
    p = sympy.Poly(list(reversed(phi)), X, domain='ZZ')
    g = sympy.gcd(p, p.diff(X))
    return p.degree() - g.degree()

# ---------- Krylov rank ----------
def krylov_int(adj, s, d):
    """integer Krylov columns s, As, ..., A^{d-1}s (as list of rows = vectors)"""
    vecs = [list(s)]
    for _ in range(d - 1):
        v = vecs[-1]
        vecs.append([sum(v[u] for u in adj[i]) for i in range(len(adj))])
    return vecs

def rank_mod_p(vecs, p):
    rows = [[x % p for x in v] for v in vecs]
    rank = 0; ncol = len(rows[0]) if rows else 0
    col = 0
    m = len(rows)
    for col in range(ncol):
        piv = None
        for i in range(rank, m):
            if rows[i][col]:
                piv = i; break
        if piv is None: continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], p - 2, p)
        pr = [(x * inv) % p for x in rows[rank]]
        rows[rank] = pr
        for i in range(m):
            if i != rank and rows[i][col]:
                f = rows[i][col]
                ri = rows[i]
                rows[i] = [(ri[j] - f * pr[j]) % p for j in range(ncol)]
        rank += 1
        if rank == m: break
    return rank

def _content_normalize(row):
    g = 0
    for x in row:
        if x: g = gcd(g, x)
    return [x // g for x in row] if g > 1 else row

def rank_Q(vecs):
    """exact rank over Q: integer elimination with row-content normalisation (no division pitfalls)"""
    M = [_content_normalize(list(v)) for v in vecs]
    m = len(M); ncol = len(M[0]) if M else 0
    rank = 0
    for col in range(ncol):
        piv = None
        for i in range(rank, m):
            if M[i][col] != 0: piv = i; break
        if piv is None: continue
        M[rank], M[piv] = M[piv], M[rank]
        pr = M[rank]; a = pr[col]
        for i in range(rank + 1, m):
            c = M[i][col]
            if c:
                M[i] = _content_normalize([a * M[i][j] - c * pr[j] for j in range(ncol)])
        rank += 1
        if rank == m: break
    return rank

def is_good_cert(adj, s, d, exact=False):
    """True => certified good.  False => not certified (for exact=True, False means provably bad)."""
    vecs = krylov_int(adj, s, d)
    if exact:
        return rank_Q(vecs) == d
    return rank_mod_p(vecs, P1) == d and rank_mod_p(vecs, P2) == d

# ---------- Lemma S prediction (used only to CROSS-CHECK, never as a certificate) ----------
def lemmaS_prediction(a):
    """Return predicted charpoly (coeff list) from Lemma S:  R(x^2) * prod_{b>=1}(x^2-b)^{k_b-1} * x^{m0}."""
    from collections import Counter
    kk = Counter(a); B = sorted(kk)
    t = sympy.Symbol('t')
    R = sympy.prod([t - b for b in B]) - sum(kk[b] * sympy.prod([t - c for c in B if c != b]) for b in B)
    k0 = kk.get(0, 0)
    if k0 >= 1:
        m0 = sum(ai - 1 for ai in a if ai >= 1) + (k0 - 1)
    else:
        m0 = 1 + sum(ai - 1 for ai in a)
    pred = sympy.expand(R.subs(t, X**2) * sympy.prod([(X**2 - b)**(kk[b] - 1) for b in B if b >= 1]) * X**m0)
    dS = 2 * len(B) + 2 * sum(1 for b in B if b >= 1 and kk[b] >= 2) + (1 if m0 > 0 else 0)
    return sympy.Poly(pred, X), dS, m0
