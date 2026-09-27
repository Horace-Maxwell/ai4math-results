# Utilities for rooted trees of height <= 2 ("diameter <= 4"): T(a), a = (a_1..a_k) multiset of leaf counts.
# Vertex 0 = centre c; vertices 1..k = v_i; then leaves of v_1, v_2, ...
import os, sys, itertools, sympy
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'code'))
from swtrees_A import charpoly, exact_rank, krylov_rows
x = sympy.Symbol('x')

def partitions_multiset(total_leaves, k, maxpart):
    if k == 0:
        if total_leaves == 0: yield ()
        return
    for first in range(min(maxpart, total_leaves), -1, -1):
        for rest in partitions_multiset(total_leaves - first, k - 1, first):
            yield (first,) + rest

def all_ht2(n):
    """all multisets a (nonincreasing) with 1 + k + sum(a) = n, k >= 1"""
    for k in range(1, n):
        L = n - 1 - k
        if L < 0: continue
        for a in partitions_multiset(L, k, L):
            yield a

def build(a):
    k = len(a); n = 1 + k + sum(a)
    adj = [[] for _ in range(n)]
    leaves = []   # leaves[i] = list of leaf vertex ids of branch i
    nxt = k + 1
    for i in range(k):
        v = i + 1
        adj[0].append(v); adj[v].append(0)
        L = []
        for _ in range(a[i]):
            adj[v].append(nxt); adj[nxt].append(v); L.append(nxt); nxt += 1
        leaves.append(L)
    return adj, leaves

_dcache = {}
def dval(a, adj):
    if a in _dcache: return _dcache[a]
    n = len(adj)
    phi = charpoly(adj, n)
    P = sympy.Poly(list(reversed(phi)), x, domain='ZZ')
    d = n - sympy.gcd(P, P.diff(x)).degree()
    _dcache[a] = d
    return d

def is_good(a, s, adj=None):
    if adj is None: adj, _ = build(a)
    d = dval(a, adj)
    return exact_rank(krylov_rows(adj, s, d)) == d

def make_s(a, sc, sigma, mu):
    """sc: centre sign; sigma[i]: sign of v_i; mu[i]: number of leaves of v_i with sign -1 (others +1)"""
    adj, leaves = build(a)
    n = len(adj); s = [1] * n
    s[0] = sc
    for i in range(len(a)):
        s[i + 1] = sigma[i]
        for j, l in enumerate(leaves[i]):
            s[l] = -1 if j < mu[i] else 1
    return s, adj
