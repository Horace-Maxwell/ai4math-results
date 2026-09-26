"""Fixed-gamma, large-n comparison for d = 3: unions of a block H vs unions of K_{3,3}.
Exact counts via polynomial powers of the block generating polynomial sum_s N_H(s) x^s."""
import networkx as nx
from ecount import dist_dp, K
from fractions import Fraction

def poly(G):
    n = G.number_of_nodes(); G = nx.convert_node_labels_to_integers(G)
    return [int(x) for x in dist_dp(n, [tuple(e) for e in G.edges()])], n

def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] += x * y
    return out

def ppow(a, k):
    r = [1]
    for _ in range(k): r = pmul(r, a)
    return r

blocks = {
  'K33': nx.complete_bipartite_graph(3, 3),
  'prism(K3xK2)': nx.circular_ladder_graph(3),
  'C6xK2(hex prism)': nx.circular_ladder_graph(6),
  'Franklin': nx.LCF_graph(12, [5, -5], 6),
  'K4': nx.complete_graph(4),
  'Pappus': nx.pappus_graph(),
  'Petersen': nx.petersen_graph(),
  'Heawood': nx.heawood_graph(),
}
for name, G in blocks.items():
    tri = sum(nx.triangles(G).values()) // 3
    c4 = sum(1 for _ in nx.simple_cycles(G, length_bound=4) if True) if False else None
    print(name, G.number_of_nodes(), 'nodes; girth', nx.girth(G), '; triangles', tri)

PK, nK = poly(blocks['K33'])
d = 3
for name in ['C6xK2(hex prism)', 'Franklin', 'Pappus', 'prism(K3xK2)', 'K4']:
    PH, nH = poly(blocks[name])
    import math
    L = nK * nH // math.gcd(nK, nH)
    print(f"\n== {name} (|H|={nH}) vs K33, n multiple of {L}")
    for gnum, gden in [(3, 16), (1, 5), (1, 4), (3, 10), (7, 20), (2, 5), (9, 20)]:
        row = []
        for mult in [1, 2, 3, 4, 6, 8, 10]:
            n = L * mult
            if n > 240: break
            t = (gnum * d * n) // gden   # floor(gamma d n)
            A = ppow(PH, n // nH); B = ppow(PK, n // nK)
            iA = sum(A[:t + 1]); iB = sum(B[:t + 1])
            row.append(f"n={n}:{'H' if iA > iB else ('=' if iA == iB else 'K')}")
        print(f"   gamma={gnum}/{gden}: " + ' '.join(row))
