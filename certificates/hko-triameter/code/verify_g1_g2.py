#!/usr/bin/env python3
"""Independent verification of the two 8-vertex counterexamples (HKO arXiv:2103.10806, Problems 1-2).

Implementation independent of the scout's code and of median_enum.c:
  * distances by Floyd-Warshall (exact integers), not BFS, no networkx;
  * median test straight from the definition quoted in HKO Sec. 2:
      |[u,v] ∩ [u,w] ∩ [v,w]| = 1 for every triple (u,v,w) of vertices (repetitions allowed);
  * tr(G) = max_{a,b,c} d(a,b)+d(a,c)+d(b,c) over all ordered triples (repetitions allowed);
  * peripheral: ecc(v) = diam(G) (equivalently: v lies in a diametral pair, HKO's wording).
Also prints the distance tables used in the Lean file and their SHA-256.
"""
import hashlib, itertools, json, sys

INF = 10**9

G1 = [(0, 1), (0, 2), (0, 4), (0, 6), (1, 3), (2, 3), (2, 5), (4, 5), (4, 7), (6, 7)]
G2 = [(0, 2), (0, 3), (0, 6), (1, 2), (2, 5), (3, 4), (3, 5), (6, 7)]


def floyd(n, edges):
    d = [[0 if i == j else INF for j in range(n)] for i in range(n)]
    for u, v in edges:
        assert u != v
        d[u][v] = d[v][u] = 1
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if d[i][k] + d[k][j] < d[i][j]:
                    d[i][j] = d[i][k] + d[k][j]
    assert all(d[i][j] < INF for i in range(n) for j in range(n)), "disconnected"
    return d


def analyse(name, n, edges):
    d = floyd(n, edges)
    V = range(n)
    interval = lambda u, v: {x for x in V if d[u][x] + d[x][v] == d[u][v]}
    medians = {}
    for u, v, w in itertools.product(V, repeat=3):
        m = interval(u, v) & interval(u, w) & interval(v, w)
        medians[(u, v, w)] = m
    is_median = all(len(m) == 1 for m in medians.values())
    bad_med = [(t, sorted(m)) for t, m in medians.items() if len(m) != 1][:3]
    ecc = [max(d[v]) for v in V]
    diam = max(ecc)
    per = [v for v in V if ecc[v] == diam]
    per_pair_def = [v for v in V if any(d[v][w] == diam for w in V)]
    assert per == per_pair_def
    s = lambda a, b, c: d[a][b] + d[a][c] + d[b][c]
    tr = max(s(a, b, c) for a, b, c in itertools.product(V, repeat=3))
    tri = [t for t in itertools.product(V, repeat=3) if s(*t) == tr]
    tri_sets = sorted({tuple(sorted(t)) for t in tri})
    q3p_viol = sorted({tuple(sorted(t)) for t in tri if not any(x in per for x in t)})
    q3_viol = sorted({tuple(sorted(t)) for t in tri
                      if not any(d[t[i]][t[j]] == diam for i, j in ((0, 1), (0, 2), (1, 2)))})
    dpairs = sorted({tuple(sorted((x, y))) for x in V for y in V if d[x][y] == diam})
    q4_viol = [p for p in dpairs if not any(s(p[0], p[1], z) == tr for z in V)]
    q4_best = {p: max(s(p[0], p[1], z) for z in V) for p in dpairs}
    out = dict(name=name, n=n, edges=edges, m=len(edges), bipartite_check=None,
               distance_matrix=d, ecc=ecc, diam=diam, peripheral=per, tr=tr,
               triametral_triples_as_sets=tri_sets, is_median=is_median, median_failures=bad_med,
               Q3prime_violations=q3p_viol, Q3_violations=q3_viol, diametral_pairs=dpairs,
               Q4_violations=q4_viol, best_extension_sum_per_diametral_pair={str(k): v for k, v in q4_best.items()})
    # 2-colouring sanity (median graphs are bipartite)
    col = [d[0][v] % 2 for v in V]
    out['bipartite_check'] = all(col[u] != col[v] for u, v in edges)
    return out


if __name__ == '__main__':
    res = [analyse('G1 (Problem 1)', 8, G1), analyse('G2 (Problem 2)', 8, G2)]
    for r in res:
        print('==', r['name'])
        for k in ['edges', 'm', 'is_median', 'median_failures', 'bipartite_check', 'ecc', 'diam',
                  'peripheral', 'tr', 'triametral_triples_as_sets', 'Q3prime_violations', 'Q3_violations',
                  'diametral_pairs', 'Q4_violations', 'best_extension_sum_per_diametral_pair']:
            print(f'  {k}: {r[k]}')
        print('  distance matrix:')
        for row in r['distance_matrix']:
            print('   ', row)
        tbl = '[' + ',\n '.join('[' + ', '.join(map(str, row)) + ']' for row in r['distance_matrix']) + ']'
        print('  lean table sha256:', hashlib.sha256(tbl.encode()).hexdigest())
    json.dump(res, open(sys.argv[1] if len(sys.argv) > 1 else '/dev/null', 'w'), indent=1, default=str)
