#!/usr/bin/env python3
"""HKO Section 3.2 figure (fig-0, LaTeX lines 257-301): x=0, m1=1, b=2, m3=3, m4=4, y=5, t1=6, a=7,
t3=8, b1=9, c=10, b3=11. Edges from the tikz code. Check tr, diam, Q3, Q3', Q4, and the four-point condition."""
import itertools
from dh_explore import bfs_all
E = [(0,1),(1,2),(2,3),(3,4),(4,5),(0,6),(0,9),(9,10),(10,11),(6,7),(7,8),(8,4),(11,4)]
n = 12
adj = [set() for _ in range(n)]
for u, v in E: adj[u].add(v); adj[v].add(u)
D = bfs_all(adj)
ecc = [max(r) for r in D]; diam = max(ecc); per = {v for v in range(n) if ecc[v] == diam}
tr = max(D[a][b]+D[a][c]+D[b][c] for a,b,c in itertools.combinations(range(n),3))
tri = [t for t in itertools.combinations(range(n),3) if D[t[0]][t[1]]+D[t[0]][t[2]]+D[t[1]][t[2]]==tr]
pairs = [(x,y) for x,y in itertools.combinations(range(n),2) if D[x][y]==diam]
q3 = all(max(D[a][b],D[a][c],D[b][c])==diam for a,b,c in tri)
q3p = all(set(t)&per for t in tri)
q4 = all(any(D[x][y]+D[x][z]+D[y][z]==tr for z in range(n)) for x,y in pairs)
fp = lambda A,B,C: (A==B and C<=A+2) or (A==C and B<=A+2) or (B==C and A<=B+2)
fpok = all(fp(D[a][b]+D[c][d],D[a][c]+D[b][d],D[a][d]+D[b][c]) for a,b,c,d in itertools.combinations(range(n),4))
print(f'diam={diam} tr={tr} peripheral={sorted(per)} triametral={tri} pairs={pairs}')
print(f'Q3={q3} Q3prime={q3p} Q4={q4} fourpoint={fpok}  (a,b,c = 7,2,10; x,y = 0,5)')
