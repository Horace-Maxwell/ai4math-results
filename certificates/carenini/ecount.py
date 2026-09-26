"""Exact edge-count distributions of induced subgraphs.

N_G(s) = #{A subset V(G) : e_G(A) = s};  i_t(G) = sum_{s<=t} N_G(s).
Two independent implementations:
  dist_dp    : numpy DP over bitmasks, e(A u {i}) = e(A) + |N(i) & A| for A below bit i
  dist_brute : plain python, loops over all subsets and all edges (small n only)
Graphs are given as (n, edge list) with vertices 0..n-1.
"""
import numpy as np
from itertools import combinations

_POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int32)

def _popcount(x):
    x = x.astype(np.int64)
    return (_POP16[x & 0xFFFF] + _POP16[(x >> 16) & 0xFFFF]
            + _POP16[(x >> 32) & 0xFFFF] + _POP16[(x >> 48) & 0xFFFF])

def dist_dp(n, edges):
    nb = [0] * n
    for u, v in edges:
        assert u != v
        nb[u] |= 1 << v
        nb[v] |= 1 << u
    e = np.zeros(1 << n, dtype=np.int32)
    for i in range(n):
        low = np.arange(1 << i, dtype=np.int64)
        e[1 << i: 1 << (i + 1)] = e[: 1 << i] + _popcount(low & (nb[i] & ((1 << i) - 1)))
    return np.bincount(e, minlength=len(edges) + 1).astype(object)

def dist_brute(n, edges):
    N = [0] * (len(edges) + 1)
    for mask in range(1 << n):
        s = 0
        for u, v in edges:
            if (mask >> u) & 1 and (mask >> v) & 1:
                s += 1
        N[s] += 1
    return N

def cdf(N):
    out, acc = [], 0
    for x in N:
        acc += int(x)
        out.append(acc)
    return out

def is_regular(n, edges, d):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1; deg[v] += 1
    return all(x == d for x in deg) and len(set(map(frozenset, edges))) == len(edges)

# ---- graph constructions -------------------------------------------------
def K(d, d2=None):
    d2 = d if d2 is None else d2
    return d + d2, [(i, d + j) for i in range(d) for j in range(d2)]

def prism_Kd(d):
    """K_d x K_2: vertices (i,s) -> i + d*s; cliques on each layer + matching."""
    E = [(i, j) for i, j in combinations(range(d), 2)]
    E += [(d + i, d + j) for i, j in combinations(range(d), 2)]
    E += [(i, d + i) for i in range(d)]
    return 2 * d, E

def clique(k):
    return k, list(combinations(range(k), 2))

def cycle(k):
    return k, [(i, (i + 1) % k) for i in range(k)]

def disjoint_union(*gs):
    n, E = 0, []
    for m, F in gs:
        E += [(u + n, v + n) for u, v in F]
        n += m
    return n, E

def switched_Kdd(d, k=1):
    """K_{d,d} (sides 0..d-1, d..2d-1) with k disjoint switches:
    remove (u,u'),(v,v') cross edges, add (u,v) and (u',v') inside the sides."""
    n, E = K(d)
    E = set(frozenset(e) for e in E)
    for s in range(k):
        u, v = 2 * s, 2 * s + 1          # left side
        up, vp = d + 2 * s, d + 2 * s + 1  # right side
        E -= {frozenset((u, up)), frozenset((v, vp))}
        E |= {frozenset((u, v)), frozenset((up, vp))}
    return n, [tuple(sorted(e)) for e in E]
