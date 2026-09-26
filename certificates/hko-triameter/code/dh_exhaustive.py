#!/usr/bin/env python3
"""Exhaustive check over all connected distance-hereditary graphs with n <= NMAX vertices.

Graph list: the scout's generator (one-vertex extensions: pendant / false twin / true twin,
isomorphism dedup via networkx) in triameter_check.py, copied unchanged into this folder from the
scout's work/round6/scouting/journal-conjectures/.
All properties below are computed by our own BFS code (no networkx distance calls).

Checks per graph G (tr over distinct triples; n >= 3):
  FP    sharp Bandelt-Mulder four-point condition on all 4-sets (only for n <= FPMAX)
  S*    for every triametral triple {a,b,c} whose three distances are all < diam and every
        diametral pair {x,y}: max(d(a,x,y), d(b,x,y), d(c,x,y)) = tr          [Theorem B]
  Q3 or Q4 (per graph)                                                          [Cor. B1]
  Q3' or Q4 (per graph) = HKO Problem 3                                         [Cor. B2]
Also counts graphs with tr > 2 diam violating Q3' (the scout's proposed reduction).
"""
import itertools, os, sys, time
from collections import deque
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # local import: triameter_check.py is in this folder
from triameter_check import dh_graphs   # scout's generator (networkx iso dedup)


def bfs_all(adj, n):
    D = []
    for s in range(n):
        d = [-1] * n; d[s] = 0; q = deque([s])
        while q:
            u = q.popleft()
            for w in adj[u]:
                if d[w] < 0:
                    d[w] = d[u] + 1; q.append(w)
        D.append(d)
    return D


def fp(A, B, C):
    return (A == B and C <= A + 2) or (A == C and B <= A + 2) or (B == C and A <= B + 2)


NMAX = int(sys.argv[1]); FPMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 10
t0 = time.time()
for n, gs in dh_graphs(NMAX):
    st = dict(graphs=0, fp_fail=0, Sstar_cases=0, Sstar_fail=0, q3_or_q4_fail=0, q3p_or_q4_fail=0,
              q3_fail=0, q3p_fail=0, q4_fail=0, reduction_fail=0)
    for G in gs:
        V = sorted(G.nodes()); idx = {v: i for i, v in enumerate(V)}
        adj = [[idx[w] for w in G.neighbors(v)] for v in V]
        D = bfs_all(adj, n)
        assert all(x >= 0 for r in D for x in r)
        st['graphs'] += 1
        if n <= FPMAX:
            for a, b, c, d in itertools.combinations(range(n), 4):
                if not fp(D[a][b] + D[c][d], D[a][c] + D[b][d], D[a][d] + D[b][c]):
                    st['fp_fail'] += 1; break
        if n < 3:
            continue
        ecc = [max(r) for r in D]; diam = max(ecc); per = {v for v in range(n) if ecc[v] == diam}
        tr = 0; tri = []
        for a, b, c in itertools.combinations(range(n), 3):
            s = D[a][b] + D[a][c] + D[b][c]
            if s > tr: tr, tri = s, [(a, b, c)]
            elif s == tr: tri.append((a, b, c))
        pairs = [(x, y) for x, y in itertools.combinations(range(n), 2) if D[x][y] == diam]
        q3 = all(max(D[a][b], D[a][c], D[b][c]) == diam for a, b, c in tri)
        q3p = all(any(u in per for u in t) for t in tri)
        q4 = all(any(D[x][y] + D[x][z] + D[y][z] == tr for z in range(n) if z not in (x, y)) for x, y in pairs)
        for a, b, c in tri:
            if max(D[a][b], D[a][c], D[b][c]) < diam:
                for x, y in pairs:
                    st['Sstar_cases'] += 1
                    if max(D[u][x] + D[u][y] + diam for u in (a, b, c)) != tr:
                        st['Sstar_fail'] += 1
        st['q3_fail'] += not q3; st['q3p_fail'] += not q3p; st['q4_fail'] += not q4
        st['q3_or_q4_fail'] += not (q3 or q4); st['q3p_or_q4_fail'] += not (q3p or q4)
        st['reduction_fail'] += (tr > 2 * diam and not q3p)
    print('n=%d' % n, st, 'elapsed %.0fs' % (time.time() - t0), flush=True)
