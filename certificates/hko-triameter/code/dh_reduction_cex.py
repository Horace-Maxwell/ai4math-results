#!/usr/bin/env python3
"""Print every connected DH graph with n <= NMAX that has tr > 2 diam but violates Q3'
(counterexamples to the scout's proposed reduction; Problem 3 still holds there via Q4)."""
import itertools, os, sys
from collections import deque
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # local import: triameter_check.py is in this folder
from triameter_check import dh_graphs
NMAX = int(sys.argv[1])
for n, gs in dh_graphs(NMAX):
    if n < 3: continue
    for G in gs:
        V = sorted(G.nodes()); idx = {v: i for i, v in enumerate(V)}
        adj = [[idx[w] for w in G.neighbors(v)] for v in V]
        D = []
        for s in range(n):
            d = [-1] * n; d[s] = 0; q = deque([s])
            while q:
                u = q.popleft()
                for w in adj[u]:
                    if d[w] < 0: d[w] = d[u] + 1; q.append(w)
            D.append(d)
        ecc = [max(r) for r in D]; diam = max(ecc); per = {v for v in range(n) if ecc[v] == diam}
        tr = max(D[a][b] + D[a][c] + D[b][c] for a, b, c in itertools.combinations(range(n), 3))
        if tr <= 2 * diam: continue
        bad = [(a, b, c) for a, b, c in itertools.combinations(range(n), 3)
               if D[a][b] + D[a][c] + D[b][c] == tr and not ({a, b, c} & per)]
        if bad:
            E = sorted((idx[u], idx[v]) if idx[u] < idx[v] else (idx[v], idx[u]) for u, v in G.edges())
            pairs = [(x, y) for x, y in itertools.combinations(range(n), 2) if D[x][y] == diam]
            print(f'n={n} diam={diam} tr={tr} edges={E}')
            print(f'  triametral triples without peripheral vertex: {bad}; ecc={ecc}')
            print(f'  diametral pairs {pairs}; extensions: ' +
                  str({p: [z for z in range(n) if D[p[0]][p[1]] + D[p[0]][z] + D[p[1]][z] == tr] for p in pairs}), flush=True)
