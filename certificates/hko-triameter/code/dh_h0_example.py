#!/usr/bin/env python3
"""Dissect a random DH graph with tr > 2 diam where some triametral triple has no peripheral vertex."""
import itertools, sys
from dh_explore import bfs_all, fourpoint_ok, props
E = [(0, 1), (0, 7), (0, 9), (0, 10), (0, 16), (0, 17), (0, 18), (1, 2), (1, 3), (1, 6), (1, 8), (1, 9), (1, 12), (2, 4), (2, 7), (2, 9), (2, 10), (2, 15), (2, 16), (2, 18), (3, 5), (3, 7), (3, 9), (3, 10), (3, 11), (3, 16), (3, 18), (4, 15), (6, 7), (6, 9), (6, 10), (6, 16), (6, 18), (7, 8), (7, 10), (7, 12), (7, 16), (7, 18), (7, 19), (8, 9), (8, 10), (8, 16), (8, 18), (9, 12), (9, 13), (10, 12), (10, 18), (12, 16), (12, 18), (13, 14), (16, 18)]
n = 20
adj = [set() for _ in range(n)]
for u, v in E: adj[u].add(v); adj[v].add(u)
D = bfs_all(adj)
print('four-point (sharp BM) holds:', fourpoint_ok(D, n))
# forbidden induced subgraph test for DH (house, gem, domino, holes C_k k>=5) by brute force up to 6 vertices + hole search
def induced(S):
    return {(u, v) for u in S for v in S if u < v and v in adj[u]}
p = props(D, n)
print('diam', p['diam'], 'tr', p['tr'], 'ecc', p['ecc'])
print('peripheral', sorted(p['per']))
bad = [t for t in p['tri'] if not any(x in p['per'] for x in t)]
print('#triametral', len(p['tri']), 'triples w/o peripheral:', bad)
for t in bad[:3]:
    a, b, c = t
    print('  triple', t, 'dists', D[a][b], D[a][c], D[b][c], 'eccs', [p['ecc'][x] for x in t])
pairs = [(x, y) for x, y in itertools.combinations(range(n), 2) if D[x][y] == p['diam']]
print('diametral pairs', pairs)
for x, y in pairs:
    best = max(D[x][y] + D[x][z] + D[y][z] for z in range(n) if z not in (x, y))
    print('  pair', (x, y), 'best extension', best)
print('Q3p', p['q3p'], 'Q4', p['q4'])
