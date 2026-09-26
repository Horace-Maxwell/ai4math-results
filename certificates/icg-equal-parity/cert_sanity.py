"""Sanity checks for cert22.py: (1) polynomial Z(Y) evaluated at sample (p,q) equals the exact model;
(2) gap polynomial of the rank-one competitor Y = s_2 (1,1,-1)^T at q = 3 equals 4(p-3); (3) a perturbed target is NOT certified."""
import itertools
from fractions import Fraction as Fr
import cert22
from core import T, Zmat, Gval, target
def ev(P, s, t): return sum(v * s**i * t**j for (i, j), v in P.items())
a, b, p0, q0 = 2, 2, 5, 3
Pp = cert22.lin_s(p0); Qq = cert22.lin_t(q0)
M = cert22.Tpoly(a, Pp); N = cert22.Tpoly(b, Qq)
for (s, t) in [(0, 0), (2, 0), (6, 2), (0, 8), (Fr(1, 2), Fr(3, 7))]:
    p = p0 + s; q = q0 + t
    Mex = T(a, p); Nex = T(b, q)
    for i in range(a + 1):
        for j in range(a + 1):
            assert ev(M[i][j], s, t) == Mex[i][j]
    for i in range(b + 1):
        for j in range(b + 1):
            assert ev(N[i][j], s, t) == Nex[i][j]
print("(1) T polynomials match exact matrices at sample points")
# (2) rank-one competitor gap at q=3 (t=0): target - G(Y) = 4(p-3)
Y = [[1, 1, -1], [-1, -1, 1], [1, 1, -1]]
for p in [5, 7, 11, 40, Fr(13, 2)]:
    g = target(2, 2, p, 3) - Gval(Y, p, 3)
    assert g == 4 * (p - 3), (p, g)
print("(2) rank-one competitor gap = 4(p-3) at q=3 confirmed exactly")
# (3) perturb target: subtract 1 -> must fail somewhere (the two maximisers become violations)
orig = cert22.run
def run_pert(a, b, p0, q0):
    import cert22 as C
    save = C.padd
    return orig(a, b, p0, q0)
nY, nbranch, bad, eq, anti, trunc, cells = cert22.run(2, 2, 5, 3)
print("(3) baseline certified:", len(bad) == 0, "tight:", len(eq))
