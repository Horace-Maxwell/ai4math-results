from ecount import *
import networkx as nx
def Hd(d):
    n, E = disjoint_union(K(d), K(d)); E = set(frozenset(e) for e in E)
    x1, y1, x2, y2 = 0, d, 2*d, 3*d
    E -= {frozenset((x1, y1)), frozenset((x2, y2))}; E |= {frozenset((x1, y2)), frozenset((x2, y1))}
    return n, [tuple(sorted(e)) for e in E]
for d in (2, 3, 4):
    G = Hd(d); assert is_regular(*G, d)
    g = nx.Graph(G[1]); assert nx.is_bipartite(g) and nx.is_connected(g)
    cH = cdf(dist_dp(*G)); cK = cdf(dist_dp(*disjoint_union(K(d), K(d))))
    wins = [t for t in range(len(cK)) if cH[t] > cK[t]]
    print(f"d={d} n={4*d}: H_d (bipartite, connected) beats 2K_dd at t = {wins}")
    for t in wins[:6]: print(f"      t={t}: i_t(H_d)={cH[t]}  i_t(2K_dd)={cK[t]}")
# Theorem A small numbers
for name, G in [('2C4', disjoint_union(cycle(4), cycle(4))), ('C8', cycle(8)), ('C3+C5', disjoint_union(cycle(3), cycle(5)))]:
    print(name, 'i_3 =', cdf(dist_dp(*G))[3])
for name, G in [('2K33', disjoint_union(K(3), K(3))), ('3K4', disjoint_union(clique(4), clique(4), clique(4))), ('S3+K33', disjoint_union(switched_Kdd(3,1), K(3)))]:
    c = cdf(dist_dp(*G)); print(name, 'i_1 =', c[1], ' i_10 =', c[10], ' i_9 =', c[9])
for name, G in [('K44', K(4)), ('S4', switched_Kdd(4,1)), ('prism K4xK2', prism_Kd(4))]:
    c = cdf(dist_dp(*G)); print(name, 'i_1 =', c[1], ' i_5 =', c[5])
for name, G in [('K55', K(5)), ('S5', switched_Kdd(5,1))]:
    c = cdf(dist_dp(*G)); print(name, 'i_1 =', c[1], ' i_11 =', c[11])
