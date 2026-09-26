#!/usr/bin/env python3
"""Test candidate lemma S on random connected DH graphs:
S: if {a,b,c} is triametral and none of a,b,c is peripheral, then for EVERY diametral pair {x,y}
   max(d(a,x,y), d(b,x,y), d(c,x,y)) = tr(G).
S implies HKO Problem 3 (per-graph 'Q3' or Q4').
Also records S_all: the same conclusion for all triametral triples (known false: Fig.1 H)."""
import itertools, random, sys
from dh_explore import bfs_all, random_dh
rng = random.Random(int(sys.argv[1])); trials = int(sys.argv[2])
nmin, nmax = int(sys.argv[3]), int(sys.argv[4])
st = dict(graphs=0, with_nonper_triple=0, S_fail=0, Sall_fail=0, P3_fail=0)
ex = None
for t in range(trials):
    n = rng.randint(nmin, nmax)
    wp = rng.choice([(0.5, 0.25, 0.25), (0.7, 0.15, 0.15), (0.34, 0.33, 0.33), (0.6, 0.3, 0.1), (0.6, 0.1, 0.3), (0.8, 0.1, 0.1)])
    adj = random_dh(n, rng, wp); D = bfs_all(adj); st['graphs'] += 1
    ecc = [max(r) for r in D]; diam = max(ecc); per = {v for v in range(n) if ecc[v] == diam}
    tr = max(D[a][b] + D[a][c] + D[b][c] for a, b, c in itertools.combinations(range(n), 3))
    tri = [(a, b, c) for a, b, c in itertools.combinations(range(n), 3) if D[a][b] + D[a][c] + D[b][c] == tr]
    pairs = [(x, y) for x, y in itertools.combinations(range(n), 2) if D[x][y] == diam]
    q3p = all(any(u in per for u in T) for T in tri)
    q4 = all(any(D[x][y] + D[x][z] + D[y][z] == tr for z in range(n) if z not in (x, y)) for x, y in pairs)
    if not (q3p or q4): st['P3_fail'] += 1; print('P3 COUNTEREXAMPLE', n, sorted((u, w) for u in range(n) for w in adj[u] if u < w), flush=True)
    sall = all(max(D[u][x] + D[u][y] + diam for u in T) == tr for T in tri for x, y in pairs)
    if not sall: st['Sall_fail'] += 1
    bad = [T for T in tri if not any(u in per for u in T)]
    if bad:
        st['with_nonper_triple'] += 1
        ok = all(max(D[u][x] + D[u][y] + diam for u in T) == tr for T in bad for x, y in pairs)
        if not ok:
            st['S_fail'] += 1
            if ex is None: ex = (n, sorted((u, w) for u in range(n) for w in adj[u] if u < w))
print(st); print('S counterexample:', ex)
