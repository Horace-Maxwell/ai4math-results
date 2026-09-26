"""Theorem D check. H_d = two copies of K_{d,d} joined by a switch:
remove x1y1 (copy 1) and x2y2 (copy 2), add x1y2 and x2y1.  d-regular, bipartite, 4d vertices.
Claim 1: Z_{2K}(q) - Z_H(q) = 2(q-1)(w0*w2 - w1^2) as polynomials in q, where
  w_ab = sum_{a',b'} C(d-1,a')C(d-1,b') q^{a'b' + a*b' + b*a'}  (w0=w_00, w1=w_10, w2=w_11).
Claim 2: (q-1)(w0 w2 - w1^2) > 0 for q != 1 (checked on a grid; proven by the FKG-type identity).
Claim 3 (consequence): for fixed gamma in (1/8,1/2) and large n, i_gamma(k H) > i_gamma(2k K)."""
import sympy as sp
from math import comb
from ecount import dist_dp, K, disjoint_union
q = sp.symbols('q')
def H(d):
    n, E = disjoint_union(K(d), K(d))   # copy1: 0..d-1 | d..2d-1 ; copy2: 2d..3d-1 | 3d..4d-1
    E = set(frozenset(e) for e in E)
    x1, y1, x2, y2 = 0, d, 2*d, 3*d
    E -= {frozenset((x1, y1)), frozenset((x2, y2))}
    E |= {frozenset((x1, y2)), frozenset((x2, y1))}
    return n, [tuple(sorted(e)) for e in E]
def Zpoly(N): return sp.expand(sum(int(c) * q**s for s, c in enumerate(N)))
for d in range(2, 6):
    nH, EH = H(d)
    ZH = Zpoly(dist_dp(nH, EH)); ZK = Zpoly(dist_dp(*K(d)))
    w = {}
    for (a, b) in [(0, 0), (1, 0), (1, 1)]:
        w[(a, b)] = sp.expand(sum(comb(d-1, i)*comb(d-1, j)*q**(i*j + a*j + b*i) for i in range(d) for j in range(d)))
    lhs = sp.expand(ZK**2 - ZH); rhs = sp.expand(2*(q-1)*(w[(0,0)]*w[(1,1)] - w[(1,0)]**2))
    ok = sp.simplify(lhs - rhs) == 0
    f = sp.lambdify(q, (q-1)*(w[(0,0)]*w[(1,1)] - w[(1,0)]**2))
    grid_ok = all(f(x) > 0 for x in [0.01*k for k in range(1, 100)] + [1 + 0.01*k for k in range(1, 1000)])
    print(f"d={d}: identity Z_2K - Z_H = 2(q-1)(w0w2-w1^2): {ok};  (q-1)(w0w2-w1^2)>0 on grid q in (0,11], q!=1: {grid_ok}")
# exact large-n comparisons for d = 2, 3
def pmul(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b): out[i+j] += x*y
    return out
def ppow(a, k):
    r = [1]
    for _ in range(k): r = pmul(r, a)
    return r
for d in (2, 3, 4):
    PH = [int(x) for x in dist_dp(*H(d))]; PK = [int(x) for x in dist_dp(*K(d))]
    for gnum, gden in [(3, 20), (1, 5), (1, 4), (1, 3), (2, 5), (9, 20)]:
        row = []
        for k in [1, 2, 4, 8, 12, 16, 24]:
            n = 4*d*k
            if n > 200: break
            t = (gnum*d*n)//gden
            A = ppow(PH, k); B = ppow(PK, 2*k)
            iA, iB = sum(A[:t+1]), sum(B[:t+1])
            row.append(f"{n}:{'H' if iA > iB else ('=' if iA == iB else 'K')}")
        print(f"  d={d} gamma={gnum}/{gden}: " + ' '.join(row))
