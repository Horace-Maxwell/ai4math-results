#!/usr/bin/env python3
"""Distance-heredity straight from the definition (Howorka; HKO Sec. 3.2):
G is DH iff G is connected and every connected induced subgraph H is isometric (d_H = d_G on V(H)).
Brute force over all 2^n vertex subsets (fine for n <= 12). Independent of the one-vertex-extension
generator and of the Bandelt-Mulder four-point theorem.  Also recomputes diam, tr, Q3, Q3', Q4.
Usage: dh_by_definition.py  (runs the built-in test graphs)  |  dh_by_definition.py n 'edge list'"""
import itertools, sys, ast
from collections import deque


def dists(n, adj, S):
    """BFS distances inside the induced subgraph on vertex set S (bitmask); -1 if unreachable."""
    verts = [v for v in range(n) if S >> v & 1]
    D = {}
    for s in verts:
        d = {s: 0}; q = deque([s])
        while q:
            u = q.popleft()
            for w in adj[u]:
                if (S >> w & 1) and w not in d:
                    d[w] = d[u] + 1; q.append(w)
        D[s] = d
    return verts, D


def is_dh(n, E):
    adj = [set() for _ in range(n)]
    for u, v in E: adj[u].add(v); adj[v].add(u)
    full = (1 << n) - 1
    verts, DG = dists(n, adj, full)
    if any(len(DG[s]) != n for s in verts):
        return False, 'disconnected'
    for S in range(1, full):
        vs, DH = dists(n, adj, S)
        if any(len(DH[s]) != len(vs) for s in vs):
            continue  # H not connected
        for s in vs:
            for t, dt in DH[s].items():
                if dt != DG[s][t]:
                    return False, f'induced subgraph {vs} not isometric at ({s},{t}): {dt} vs {DG[s][t]}'
    return True, ''


def props(n, E):
    adj = [set() for _ in range(n)]
    for u, v in E: adj[u].add(v); adj[v].add(u)
    _, DD = dists(n, adj, (1 << n) - 1)
    D = [[DD[i][j] for j in range(n)] for i in range(n)]
    ecc = [max(r) for r in D]; diam = max(ecc); per = {v for v in range(n) if ecc[v] == diam}
    tr = max(D[a][b] + D[a][c] + D[b][c] for a, b, c in itertools.combinations(range(n), 3))
    tri = [t for t in itertools.combinations(range(n), 3) if D[t[0]][t[1]] + D[t[0]][t[2]] + D[t[1]][t[2]] == tr]
    pairs = [(x, y) for x, y in itertools.combinations(range(n), 2) if D[x][y] == diam]
    q3 = all(max(D[a][b], D[a][c], D[b][c]) == diam for a, b, c in tri)
    q3p = all(set(t) & per for t in tri)
    q4 = all(any(D[x][y] + D[x][z] + D[y][z] == tr for z in range(n) if z not in (x, y)) for x, y in pairs)
    return dict(diam=diam, tr=tr, Q3=q3, Q3prime=q3p, Q4=q4,
                bad_Q3prime=[t for t in tri if not set(t) & per])


TESTS = {
    'HKO Fig1 G (DH)': (6, [(0, 1), (1, 2), (1, 3), (1, 4), (2, 5), (3, 5), (4, 5)]),
    'HKO Fig1 H (DH)': (6, [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)]),
    'G2 (median, DH?)': (8, [(0, 2), (0, 3), (0, 6), (1, 2), (2, 5), (3, 4), (3, 5), (6, 7)]),
    'G1 (median, domino => not DH)': (8, [(0, 1), (0, 2), (0, 4), (0, 6), (1, 3), (2, 3), (2, 5), (4, 5), (4, 7), (6, 7)]),
    'C5 (not DH)': (5, [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]),
    'HKO Sec3.2 fig (not DH)': (12, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 6), (0, 9), (9, 10), (10, 11), (6, 7), (7, 8), (8, 4), (11, 4)]),
}

if __name__ == '__main__':
    if len(sys.argv) > 2:
        TESTS = {'input': (int(sys.argv[1]), ast.literal_eval(sys.argv[2]))}
    for name, (n, E) in TESTS.items():
        ok, why = is_dh(n, E)
        print(f'{name}: DH={ok} {why}')
        print('   ', props(n, E))
