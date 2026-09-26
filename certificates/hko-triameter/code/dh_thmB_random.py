#!/usr/bin/env python3
"""Random test of Theorem B exactly as stated: in a connected DH graph (built by one-vertex
extensions), for every triametral triple with all three distances < diam and every diametral pair
{x,y}: max_u d(u,x,y) = tr.  Also the more general inequality: for EVERY triple {a,b,c} without a
diametral pair, max_u d(u,x,y) >= d(a,b,c).  Also Q3 or Q4."""
import itertools, random, sys
from dh_explore import bfs_all, random_dh
rng = random.Random(int(sys.argv[1])); trials = int(sys.argv[2]); nmin, nmax = int(sys.argv[3]), int(sys.argv[4])
st = dict(graphs=0, thmB_cases=0, thmB_fail=0, general_cases=0, general_fail=0, q3q4_fail=0)
for t in range(trials):
    n = rng.randint(nmin, nmax)
    wp = rng.choice([(0.5, 0.25, 0.25), (0.7, 0.15, 0.15), (0.34, 0.33, 0.33), (0.6, 0.3, 0.1), (0.6, 0.1, 0.3), (0.8, 0.1, 0.1)])
    adj = random_dh(n, rng, wp); D = bfs_all(adj); st['graphs'] += 1
    diam = max(max(r) for r in D)
    trip = list(itertools.combinations(range(n), 3))
    s = {T: D[T[0]][T[1]] + D[T[0]][T[2]] + D[T[1]][T[2]] for T in trip}
    tr = max(s.values())
    pairs = [(x, y) for x, y in itertools.combinations(range(n), 2) if D[x][y] == diam]
    nodiam = [T for T in trip if max(D[T[0]][T[1]], D[T[0]][T[2]], D[T[1]][T[2]]) < diam]
    for x, y in pairs:
        ext = [D[u][x] + D[u][y] + diam for u in range(n)]
        for T in nodiam:
            m = max(ext[T[0]], ext[T[1]], ext[T[2]])
            st['general_cases'] += 1
            if m < s[T]: st['general_fail'] += 1
            if s[T] == tr:
                st['thmB_cases'] += 1
                if m != tr: st['thmB_fail'] += 1
    q3 = all(max(D[T[0]][T[1]], D[T[0]][T[2]], D[T[1]][T[2]]) == diam for T in trip if s[T] == tr)
    q4 = all(any(D[x][y] + D[x][z] + D[y][z] == tr for z in range(n) if z not in (x, y)) for x, y in pairs)
    if not (q3 or q4): st['q3q4_fail'] += 1
print(st)
