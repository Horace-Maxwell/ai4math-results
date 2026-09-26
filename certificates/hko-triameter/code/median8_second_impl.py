#!/usr/bin/env python3
"""Second, independent implementation of the n<=8 minimality/uniqueness claims (Problems 1, 2).

Generation (different from median_enum.c):
  * n <= 7: all connected graphs from the networkx graph atlas;
  * n = 8: every connected 8-vertex graph G has a non-cut vertex v (a leaf of a spanning tree), and
    G - v is a connected 7-vertex graph. So G arises from some connected atlas graph H on 7
    vertices by adding a vertex adjacent to a nonempty subset S of V(H). Pruning (justified by the
    median DEFINITION: a triangle a,b,c has [a,b]∩[a,c]∩[b,c] = ∅): H triangle-free, S independent.
Median test: straight from the definition over all ordered triples (Floyd-Warshall distances).
Isomorphism dedup: networkx.is_isomorphic.  Also reports the number of median graphs per n.
"""
import itertools, sys, time
import networkx as nx
from networkx.generators.atlas import graph_atlas_g

INF = 10**9


def dist_matrix(n, edges):
    d = [[0 if i == j else INF for j in range(n)] for i in range(n)]
    for u, v in edges:
        d[u][v] = d[v][u] = 1
    for k in range(n):
        dk = d[k]
        for i in range(n):
            di = d[i]; dik = di[k]
            if dik == INF: continue
            for j in range(n):
                if dik + dk[j] < di[j]:
                    di[j] = dik + dk[j]
    return d


def is_median(n, d):
    for u, v, w in itertools.combinations_with_replacement(range(n), 3):
        cnt = 0
        for x in range(n):
            if d[u][x] + d[x][v] == d[u][v] and d[u][x] + d[x][w] == d[u][w] and d[v][x] + d[x][w] == d[v][w]:
                cnt += 1
                if cnt > 1: return False
        if cnt != 1: return False
    return True   # (the condition is symmetric in u,v,w, so unordered triples with repetition suffice)


def q3p_q4(n, d):
    ecc = [max(r) for r in d]; diam = max(ecc); per = {v for v in range(n) if ecc[v] == diam}
    s = lambda a, b, c: d[a][b] + d[a][c] + d[b][c]
    tr = max(s(a, b, c) for a, b, c in itertools.product(range(n), repeat=3))
    q3p = all((a in per or b in per or c in per) for a, b, c in itertools.product(range(n), repeat=3) if s(a, b, c) == tr)
    q4 = all(any(s(x, y, z) == tr for z in range(n)) for x in range(n) for y in range(n) if d[x][y] == diam)
    return q3p, q4


def run():
    t0 = time.time()
    atlas = [G for G in graph_atlas_g() if G.number_of_nodes() >= 1 and nx.is_connected(G)]
    med_classes = {}
    for G in atlas:
        n = G.number_of_nodes()
        d = dist_matrix(n, list(G.edges()))
        if is_median(n, d):
            med_classes.setdefault(n, []).append(G)
            q3p, q4 = q3p_q4(n, d)
            if not (q3p and q4):
                print('VIOLATOR n<=7 !!', n, sorted(G.edges()), q3p, q4)
    for n in sorted(med_classes):
        print(f'n={n}: median graphs (atlas, up to iso) = {len(med_classes[n])}')
    # n = 8
    base = [G for G in atlas if G.number_of_nodes() == 7 and sum(nx.triangles(G).values()) == 0]
    print('connected triangle-free 7-vertex atlas graphs:', len(base))
    med8, viol3, viol4, cand = [], [], [], 0
    def add_unique(lst, H):
        for K in lst:
            if nx.is_isomorphic(H, K): return
        lst.append(H)
    for H in base:
        E = list(H.edges())
        for r in range(1, 8):
            for S in itertools.combinations(range(7), r):
                if any(H.has_edge(a, b) for a, b in itertools.combinations(S, 2)):
                    continue
                cand += 1
                E8 = E + [(7, s) for s in S]
                d = dist_matrix(8, E8)
                if not is_median(8, d):
                    continue
                G8 = nx.Graph(E8)
                add_unique(med8, G8)
                q3p, q4 = q3p_q4(8, d)
                if not q3p: add_unique(viol3, G8)
                if not q4: add_unique(viol4, G8)
    print(f'n=8: candidates {cand}; median graphs up to iso = {len(med8)}; '
          f"Q3'-violators up to iso = {len(viol3)}; Q4-violators up to iso = {len(viol4)}")
    G1 = nx.Graph([(0,1),(0,2),(0,4),(0,6),(1,3),(2,3),(2,5),(4,5),(4,7),(6,7)])
    G2 = nx.Graph([(0,2),(0,3),(0,6),(1,2),(2,5),(3,4),(3,5),(6,7)])
    print("Q3'-violator(s) isomorphic to G1:", [nx.is_isomorphic(K, G1) for K in viol3])
    print('Q4-violator(s) isomorphic to G2:', [nx.is_isomorphic(K, G2) for K in viol4])
    print('elapsed %.0fs' % (time.time() - t0))


if __name__ == '__main__':
    run()
