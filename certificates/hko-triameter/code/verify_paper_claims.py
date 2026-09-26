#!/usr/bin/env python3
"""Paper-4 agent (2026-09-26): independent re-check of every concrete graph claim stated in
note.tex.  Pure Python, BFS distances, definitions checked literally.  No networkx."""
import itertools
from collections import deque


def graph(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        assert u != v and v not in adj[u]
        adj[u].add(v); adj[v].add(u)
    return adj


def bfs_all(adj, verts=None):
    verts = list(range(len(adj))) if verts is None else list(verts)
    S = set(verts)
    D = {}
    for s in verts:
        d = {s: 0}; q = deque([s])
        while q:
            u = q.popleft()
            for w in adj[u]:
                if w in S and w not in d:
                    d[w] = d[u] + 1; q.append(w)
        D[s] = d
    return D


def props(adj):
    n = len(adj)
    D = bfs_all(adj)
    assert all(len(D[s]) == n for s in range(n)), 'disconnected'
    d = lambda u, v: D[u][v]
    ecc = [max(D[u].values()) for u in range(n)]
    diam = max(ecc)
    per = [u for u in range(n) if ecc[u] == diam]
    trip = list(itertools.product(range(n), repeat=3))
    s = {t: d(t[0], t[1]) + d(t[0], t[2]) + d(t[1], t[2]) for t in trip}
    tr = max(s.values())
    tri = [t for t in trip if s[t] == tr]
    tri_sets = sorted({tuple(sorted(t)) for t in tri})
    pairs = sorted({tuple(sorted((x, y))) for x in range(n) for y in range(n) if d(x, y) == diam})
    Q3 = all(max(d(a, b), d(a, c), d(b, c)) == diam for a, b, c in tri)
    Q3p = all(any(u in per for u in t) for t in tri)
    Q4 = all(any(s[(x, y, z)] == tr for z in range(n)) for x, y in pairs)
    Q4strong = all(any(s[(x, y, z)] == tr for z in range(n) if z not in (x, y)) for x, y in pairs)
    Q4p = all(any(s[(x, y, z)] == tr for y in range(n) for z in range(n)) for x in per)
    return dict(D=D, ecc=ecc, diam=diam, per=per, tr=tr, tri_sets=tri_sets, pairs=pairs,
                Q3=Q3, Q3p=Q3p, Q4=Q4, Q4strong=Q4strong, Q4p=Q4p)


def is_median(adj):
    n = len(adj); D = bfs_all(adj)
    I = lambda u, v, x: D[u][x] + D[x][v] == D[u][v]
    for u, v, w in itertools.product(range(n), repeat=3):
        m = [x for x in range(n) if I(u, v, x) and I(u, w, x) and I(v, w, x)]
        if len(m) != 1:
            return False, (u, v, w, m)
    return True, None


def fp(A, B, C):
    return (A == B and C <= A + 2) or (A == C and B <= A + 2) or (B == C and A <= B + 2)


def bm_sorted(A, B, C):  # Bandelt-Mulder (viii) literally: two sums equal; if the smaller two are equal, largest <= +2
    s = sorted((A, B, C))
    two_equal = s[0] == s[1] or s[1] == s[2]
    if not two_equal:
        return False
    if s[0] == s[1] and s[2] > s[1]:
        return s[2] <= s[0] + 2
    return True


def four_point(adj):
    n = len(adj); D = bfs_all(adj)
    ok_fp = ok_bm = ok_vii = True
    for u, v, w, x in itertools.product(range(n), repeat=4):
        A = D[u][v] + D[w][x]; B = D[u][w] + D[v][x]; C = D[u][x] + D[v][w]
        ok_fp &= fp(A, B, C); ok_bm &= bm_sorted(A, B, C)
        ok_vii &= (A == B or A == C or B == C)
    assert ok_fp == ok_bm
    return ok_fp, ok_vii


def is_dh_by_definition(adj):
    n = len(adj); D = bfs_all(adj)
    for mask in range(1, 1 << n):
        S = [i for i in range(n) if mask >> i & 1]
        if len(S) < 3:
            continue
        DS = bfs_all(adj, S)
        if len(DS[S[0]]) != len(S):
            continue  # induced subgraph not connected
        for a in S:
            for b in S:
                if DS[a][b] != D[a][b]:
                    return False, (S, a, b)
    return True, None


def report(name, adj, dh=True):
    p = props(adj)
    med, wit = is_median(adj)
    fpok, vii = four_point(adj)
    line = f"== {name}: n={len(adj)} m={sum(len(a) for a in adj)//2} median={med} FP(viii)={fpok} (vii)={vii}"
    if dh:
        dhok, dwit = is_dh_by_definition(adj)
        line += f" DH(def)={dhok}"
        assert dhok == fpok == vii, 'Bandelt-Mulder Thm 2 consistency'
    print(line)
    print(f"   diam={p['diam']} tr={p['tr']} ecc={p['ecc']} peripheral={p['per']}")
    print(f"   triametral (as multisets) {len(p['tri_sets'])}: {p['tri_sets']}")
    print(f"   diametral pairs: {p['pairs']}")
    print(f"   Q3={p['Q3']} Q3'={p['Q3p']} Q4={p['Q4']} Q4strong={p['Q4strong']} Q4'={p['Q4p']}")
    if not med:
        print('   non-median witness', wit)
    return p


# ---------------- G1 (Lean labels) ----------------
g1e = [(0, 1), (0, 2), (0, 4), (0, 6), (1, 3), (2, 3), (2, 5), (4, 5), (4, 7), (6, 7)]
G1 = graph(8, g1e)
p1 = report('G1', G1)
c1 = {3: (0, 0), 2: (1, 0), 5: (2, 0), 1: (0, 1), 0: (1, 1), 4: (2, 1), 6: (1, 2), 7: (2, 2)}
# grid embedding checks
l1 = lambda a, b: sum(abs(x - y) for x, y in zip(a, b))
ind = sorted(tuple(sorted((u, v))) for u in c1 for v in c1 if u < v and l1(c1[u], c1[v]) == 1)
assert ind == sorted(tuple(sorted(e)) for e in g1e), 'G1 not the induced grid graph'
assert all(p1['D'][u][v] == l1(c1[u], c1[v]) for u in c1 for v in c1), 'G1 not isometric in grid'
pts = set(c1.values())
med3 = lambda a, b, c: tuple(sorted(t)[1] for t in zip(a, b, c))
assert all(med3(a, b, c) in pts for a in pts for b in pts for c in pts), 'G1 not median-closed'
assert set(pts) == {(x, y) for x in range(3) for y in range(3)} - {(0, 2)}
print('   G1 = 3x3 grid minus corner (0,2): induced, isometric, median-closed: OK')
D1 = p1['D']
print('   d(1,5), d(1,6), d(5,6) =', D1[1][5], D1[1][6], D1[5][6], '; ecc of 1,5,6 =', [p1['ecc'][i] for i in (1, 5, 6)])
assert p1['diam'] == 4 and p1['tr'] == 8 and p1['per'] == [3, 7] and not p1['Q3p'] and not p1['Q3'] and p1['Q4']
bad = [t for t in p1['tri_sets'] if not any(u in p1['per'] for u in t)]
print('   triametral triples without peripheral vertex:', bad)
assert bad == [(1, 5, 6)]
print('   G1 FP counterexample (1,3,4,5) sums:', D1[1][3] + D1[4][5], D1[1][4] + D1[3][5], D1[1][5] + D1[3][4])
S = [3, 1, 0, 4, 5]
DS = bfs_all(G1, S)
print('   induced subgraph on 3,1,0,4,5 : d_S(3,5) =', DS[3][5], ' d_G(3,5) =', D1[3][5])

# ---------------- G2 (Lean labels) ----------------
g2e = [(0, 2), (0, 3), (0, 6), (1, 2), (2, 5), (3, 4), (3, 5), (6, 7)]
G2 = graph(8, g2e)
p2 = report('G2', G2)
c2 = {7: (-2, 0), 6: (-1, 0), 0: (0, 0), 2: (1, 0), 1: (2, 0), 3: (0, 1), 5: (1, 1), 4: (0, 2)}
ind = sorted(tuple(sorted((u, v))) for u in c2 for v in c2 if u < v and l1(c2[u], c2[v]) == 1)
assert ind == sorted(tuple(sorted(e)) for e in g2e), 'G2 not the induced grid graph'
assert all(p2['D'][u][v] == l1(c2[u], c2[v]) for u in c2 for v in c2), 'G2 not isometric in grid'
pts = set(c2.values())
assert all(med3(a, b, c) in pts for a in pts for b in pts for c in pts), 'G2 not median-closed'
print('   G2 grid embedding: induced, isometric, median-closed: OK')
D2 = p2['D']
print('   d(5,z)+d(7,z), z=0..7:', [D2[5][z] + D2[7][z] for z in range(8)])
print('   max_{y,z} d(5,y,z) =', max(D2[5][y] + D2[5][z] + D2[y][z] for y in range(8) for z in range(8)))
assert p2['tri_sets'] == [(1, 4, 7)] and p2['diam'] == 4 and p2['tr'] == 12
assert not p2['Q4'] and not p2['Q4strong'] and not p2['Q4p'] and p2['Q3'] and p2['Q3p']
# G2 from K2 by Bandelt-Mulder one-vertex extensions: 0-2; 5 pendant at 2; 3 false twin of 2; pendants 1@2, 4@3, 6@0, 7@6
seq = graph(8, [])
built = {0, 2}; E = {(0, 2)}
def add(E, new, nbrs):
    return E | {tuple(sorted((new, w))) for w in nbrs}
E = add(E, 5, [2]); E = add(E, 3, [0, 5]); E = add(E, 1, [2]); E = add(E, 4, [3]); E = add(E, 6, [0]); E = add(E, 7, [6])
assert sorted(E) == sorted(tuple(sorted(e)) for e in g2e)
print('   G2 = K2 (0-2) + pendant 5@2 + false twin 3 of 2 + pendants 1@2, 4@3, 6@0, 7@6: OK')

# ---------------- H11 ----------------
h11e = [(0, 1), (0, 2), (0, 3), (0, 5), (1, 4), (1, 6), (2, 4), (2, 7), (3, 4), (3, 8), (4, 9), (5, 10)]
H11 = graph(11, h11e)
p3 = report('H11', H11)
assert p3['diam'] == 5 and p3['tr'] == 12 and not p3['Q3p'] and not p3['Q3'] and p3['Q4']
Dh = p3['D']
print('   d(6,7),d(6,8),d(7,8) =', Dh[6][7], Dh[6][8], Dh[7][8], '; extensions of (9,10):',
      [z for z in range(11) if 5 + Dh[9][z] + Dh[10][z] == 12])

# ---------------- HKO Figure 3: G and H ----------------
# G: y=0, m=1, a=2, b=3, c=4, x=5 ; edges y-m, m-a,b,c, x-a,b,c
F3G = graph(6, [(0, 1), (1, 2), (1, 3), (1, 4), (2, 5), (3, 5), (4, 5)])
pg = report('HKO Fig.3 G', F3G)
# H: a=0,b=1,c=2,x=3,m=4,y=5 ; a,b,c ~ x,m,y ; x-m, m-y
F3H = graph(6, [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)])
ph = report('HKO Fig.3 H', F3H)
assert not pg['Q3p'] and pg['Q4'] and ph['Q3'] and not ph['Q4']

# ---------------- HKO Figure 4 (median, Q3 fails) ----------------
# a=0, m=1, c=2, b=3, x=4 ; edges a-m, m-c, m-b, b-x, x-c
F4 = graph(5, [(0, 1), (1, 2), (1, 3), (3, 4), (4, 2)])
p4 = report('HKO Fig.4', F4)

# ---------------- HKO Figure 2 (Section 3.2) ----------------
# x=0, m1=1, b=2, m3=3, m4=4, y=5, t1=6, a=7, t3=8, b1=9, c=10, b3=11
F2 = graph(12, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 6), (0, 9), (9, 10), (10, 11), (6, 7), (7, 8), (8, 4), (11, 4)])
p5 = report('HKO Fig.2', F2, dh=True)
assert not p5['Q3'] and not p5['Q3p'] and not p5['Q4']

# ---------------- MathOverflow 506536 example ----------------
names = ['s', 'u1', 'u2', 'a', 'v1', 'v2', 'b', 'x', 'w1', 'w2', 'c']
ix = {v: i for i, v in enumerate(names)}
sq = [('s', 'u1', 'a', 'u2'), ('s', 'v1', 'b', 'v2'), ('s', 'v1', 'x', 'w1'), ('s', 'w1', 'c', 'w2')]
Emo = set()
for q in sq:
    for i in range(4):
        Emo.add(tuple(sorted((ix[q[i]], ix[q[(i + 1) % 4]]))))
MO = graph(11, sorted(Emo))
p6 = report('MO 506536', MO, dh=False)
print('   triametral:', [[names[i] for i in t] for t in p6['tri_sets']], 'pairs:', [[names[i] for i in t] for t in p6['pairs']])
# the MathOverflow example is not distance-hereditary: b, v2, s, w1, x induce a path of length 4, d(b,x) = 2
Sp = [ix[v] for v in ['b', 'v2', 's', 'w1', 'x']]
ind_mo = sorted((names[u], names[w]) for u, w in itertools.combinations(Sp, 2) if w in MO[u])
Dmo = bfs_all(MO)
print('   MO induced edges on b,v2,s,w1,x:', ind_mo, '; d(b,x) =', Dmo[ix['b']][ix['x']],
      '; d in induced path =', bfs_all(MO, Sp)[ix['b']][ix['x']])
assert Dmo[ix['b']][ix['x']] == 2 and bfs_all(MO, Sp)[ix['b']][ix['x']] == 4 and len(ind_mo) == 4
print('ALL ASSERTIONS PASSED')
