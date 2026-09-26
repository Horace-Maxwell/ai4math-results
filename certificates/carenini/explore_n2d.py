import networkx as nx, random, sys
from ecount import *
random.seed(1)
def wins(G, ref):
    c = cdf(dist_dp(*G))
    return [t for t in range(len(ref)) if c[t] > ref[t]], c
for d in range(3, 11):
    n = 2 * d
    ref = cdf(dist_dp(*K(d)))
    cands = [('prism', prism_Kd(d))] + [('switch%d' % k, switched_Kdd(d, k)) for k in range(1, d // 2 + 1)]
    S = 40 if d <= 8 else 12
    for s in range(S):
        G = nx.random_regular_graph(d, n, seed=random.randrange(10**9))
        cands.append(('rand', (n, [tuple(e) for e in G.edges()])))
    allw = set(); rec = {}
    for name, G in cands:
        assert is_regular(*G, d)
        w, c = wins(G, ref)
        allw |= set(w)
        if name != 'rand': rec[name] = w
    print(f"d={d} n={n} t*={d*d-3*d+1}: failing t (union over {len(cands)} cands) = {sorted(allw)}")
    for k, v in rec.items(): print(f"     {k}: {v}")
    sys.stdout.flush()
