"""Exhaustive check at n = 2d for d = 3, 4, 5: all d-regular graphs on 2d vertices.
Enumeration: BFS over isomorphism classes under 2-switches, starting from K_{d,d}.
(Any two simple graphs with the same degree sequence are connected by 2-switches
[Hakimi 1962 / Fulkerson-Hoffman-McAndrew], so the BFS reaches every class.)
Completeness is cross-checked against the known class counts 2, 6, 60
(= #cubic graphs on 6? no: #(d-1)-regular graphs on 2d vertices, by complementation:
 2-regular on 6: 2 (C6, 2C3); 3-regular on 8: 6 (5 connected + 2K4); 4-regular on 10: 60 (59 + 2K5))."""
import networkx as nx, json, sys
from itertools import combinations
from ecount import dist_dp, cdf, K

def canon_bucket(G):
    return nx.weisfeiler_lehman_graph_hash(G, iterations=3)

def switches(G):
    E = list(G.edges())
    for (a, b), (c, dd) in combinations(E, 2):
        if len({a, b, c, dd}) < 4: continue
        for (x, y, z, w) in ((a, c, b, dd), (a, dd, b, c)):
            # replace ab, cd by xy, zw
            if G.has_edge(x, y) or G.has_edge(z, w): continue
            H = G.copy(); H.remove_edge(a, b); H.remove_edge(c, dd); H.add_edge(x, y); H.add_edge(z, w)
            yield H

def enumerate_classes(d):
    n0, E0 = K(d)
    G0 = nx.Graph(); G0.add_nodes_from(range(n0)); G0.add_edges_from(E0)
    classes = {}  # hash -> list of reps
    def add(G):
        h = canon_bucket(G)
        for R in classes.get(h, []):
            if nx.is_isomorphic(R, G): return False
        classes.setdefault(h, []).append(G); return True
    add(G0); queue = [G0]
    while queue:
        G = queue.pop()
        for H in switches(G):
            if add(H): queue.append(H)
    return [G for L in classes.values() for G in L]

expected = {3: 2, 4: 6, 5: 60}
report = {}
for d in (3, 4, 5):
    reps = enumerate_classes(d)
    n = 2 * d
    print(f"d={d}: {len(reps)} isomorphism classes of {d}-regular graphs on {n} vertices (expected {expected[d]})")
    assert len(reps) == expected[d]
    Kc = cdf(dist_dp(*K(d)))
    data = []
    for G in reps:
        c = cdf(dist_dp(n, [tuple(e) for e in G.edges()]))
        T = sum(nx.triangles(G).values()) // 3
        isK = nx.is_isomorphic(G, nx.complete_bipartite_graph(d, d))
        data.append((c, T, isK, sorted(G.edges())))
    fail = []
    for t in range(d * d + 1):
        mx = max(x[0][t] for x in data)
        if Kc[t] < mx:
            fail.append(t)
    maxers = {t: [i for i, x in enumerate(data) if x[0][t] == max(y[0][t] for y in data)] for t in range(d*d+1)}
    print(f"   thresholds t in [0,{d*d}] where K_{{d,d}} is NOT a maximiser of i_t: {fail}")
    print(f"   thresholds where K_{{d,d}} is the unique maximiser: {[t for t in range(d*d+1) if maxers[t]==[i for i,x in enumerate(data) if x[2]]]}")
    print(f"   thresholds where K_{{d,d}} ties for max with another graph: {[t for t in range(d*d+1) if t not in fail and len(maxers[t])>1]}")
    for t in fail:
        best = max(x[0][t] for x in data)
        print(f"     t={t:2d}: max i_t={best}  K_dd={Kc[t]}  #maximisers={len(maxers[t])}  (triangles of maximisers: {[data[i][1] for i in maxers[t]]})")
    report[d] = {'classes': len(reps), 'fail_t': fail, 'K_cdf': Kc}
json.dump(report, open('../logs/exhaustive_n2d.json', 'w'), indent=1)
