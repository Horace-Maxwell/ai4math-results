"""Check Theorem A: at t* = dn/2 - 3d + 1,
   i_{t*}(G) = 2^n - 1 - n - C(n,2) - n*C(d,2) + 2T(G) - Q(G),
where Q = #{4-sets with >= d+2 edges} + #{5-sets with >= 2d+2 edges}."""
import networkx as nx, random
from math import comb
from itertools import combinations
from ecount import *

def TQ(n, E):
    adj = [set() for _ in range(n)]
    for u, v in E: adj[u].add(v); adj[v].add(u)
    T = sum(1 for a, b, c in combinations(range(n), 3) if b in adj[a] and c in adj[a] and c in adj[b])
    d = len(adj[0])
    def e(S): return sum(1 for x, y in combinations(S, 2) if y in adj[x])
    Q = sum(1 for S in combinations(range(n), 4) if e(S) >= d + 2)
    Q += sum(1 for S in combinations(range(n), 5) if e(S) >= 2 * d + 2)
    return T, Q

random.seed(20260926)
checked = 0; bad = 0
cases = []
for d in range(2, 9):
    for m in range(1, 4):
        n = 2 * d * m
        if n > 20: continue
        cases.append((n, d, 'mKdd', disjoint_union(*[K(d)] * m)))
        if d >= 3:
            cases.append((n, d, 'prism+(m-1)Kdd', disjoint_union(prism_Kd(d), *[K(d)] * (m - 1))))
        if d == 2:
            cases.append((n, d, 'C_n', cycle(n)))
            if n >= 8: cases.append((n, d, 'C3+C(n-3)', disjoint_union(cycle(3), cycle(n - 3))))
        for s in range(6):
            G = nx.random_regular_graph(d, n, seed=random.randrange(10**9))
            cases.append((n, d, 'random', (n, [tuple(e) for e in G.edges()])))
        if (n % (d + 1)) == 0:
            cases.append((n, d, 'K_{d+1} union', disjoint_union(*[clique(d + 1)] * (n // (d + 1)))))
for n, d, name, G in cases:
    assert is_regular(*G, d)
    ts = d * n // 2 - 3 * d + 1
    if ts < 0: continue
    c = cdf(dist_dp(*G))
    T, Q = TQ(*G)
    pred = 2**n - 1 - n - comb(n, 2) - n * comb(d, 2) + 2 * T - Q
    ok = (c[ts] == pred)
    checked += 1; bad += (not ok)
    ref = cdf(dist_dp(*disjoint_union(*[K(d)] * (n // (2 * d)))))[ts]
    print(f"n={n:2d} d={d} t*={ts:3d} {name:16s} T={T:3d} Q={Q:2d} i_t*={c[ts]} formula={'OK' if ok else 'MISMATCH '+str(pred)}  minus mKdd = {c[ts]-ref}")
print('checked', checked, 'mismatches', bad)
