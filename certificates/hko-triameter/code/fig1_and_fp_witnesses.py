#!/usr/bin/env python3
"""Distance tables for HKO Fig. 1 graphs G, H; FP (sharp BM four-point) witnesses for G1, G2."""
import itertools
from dh_explore import bfs_all
def adjl(n, E):
    a = [set() for _ in range(n)]
    for u, v in E: a[u].add(v); a[v].add(u)
    return a
def fp(A, B, C): return (A == B and C <= A + 2) or (A == C and B <= A + 2) or (B == C and A <= B + 2)
graphs = {
 'F1G': (6, [(0, 1), (1, 2), (1, 3), (1, 4), (2, 5), (3, 5), (4, 5)]),
 'F1H': (6, [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)]),
 'G1': (8, [(0,1),(0,2),(0,4),(0,6),(1,3),(2,3),(2,5),(4,5),(4,7),(6,7)]),
 'G2': (8, [(0,2),(0,3),(0,6),(1,2),(2,5),(3,4),(3,5),(6,7)]),
}
for name, (n, E) in graphs.items():
    D = bfs_all(adjl(n, E))
    print(name, 'table:', D)
    viol = [(u, v, w, x) for u, v, w, x in itertools.product(range(n), repeat=4)
            if not fp(D[u][v] + D[w][x], D[u][w] + D[v][x], D[u][x] + D[v][w])]
    print('  FP violations (ordered quadruples):', len(viol), 'first:', viol[:3])
    if viol:
        u, v, w, x = viol[0]
        print('  sums for first:', D[u][v] + D[w][x], D[u][w] + D[v][x], D[u][x] + D[v][w])
