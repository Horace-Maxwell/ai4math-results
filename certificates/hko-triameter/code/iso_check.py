#!/usr/bin/env python3
"""Brute-force isomorphism check (all 8! bijections) between the unique n=8 violators found by
median_enum.c and the graphs G1, G2; also |Aut| of each."""
import itertools
G1 = [(0,1),(0,2),(0,4),(0,6),(1,3),(2,3),(2,5),(4,5),(4,7),(6,7)]
G2 = [(0,2),(0,3),(0,6),(1,2),(2,5),(3,4),(3,5),(6,7)]
V3 = [(0,3),(0,6),(1,2),(1,5),(2,7),(3,7),(4,5),(4,6),(5,7),(6,7)]   # Q3'-violator, median_enum n=8
V4 = [(0,3),(1,6),(2,5),(3,7),(4,5),(4,6),(5,7),(6,7)]               # Q4-violator,  median_enum n=8
def es(E): return {frozenset(e) for e in E}
def isos(A, B):
    a, b = es(A), es(B)
    if len(a) != len(b): return []
    return [p for p in itertools.permutations(range(8)) if {frozenset((p[u], p[v])) for u, v in a} == b]
for name, A, B in [("G1 vs Q3'-violator", G1, V3), ("G2 vs Q4-violator", G2, V4), ("G1 vs G1", G1, G1), ("G2 vs G2", G2, G2)]:
    I = isos(A, B)
    print(name, "isomorphisms:", len(I), "example:", I[0] if I else None)
