"""Theorem B: switched K_{d,d}  S_d = K_{d,d} - {u u', v v'} + {u v, u' v'}.
Claims: i_0(S_d) = 3*2^(d-1)+1, i_1(S_d) = 2^(d+1)+d^2+4d-9, i_1(S_d)-i_1(K_{d,d}) = 4d-8.
Also several copies: S_d + (m-1)K_{d,d} vs m K_{d,d} at t=1."""
from ecount import *
for d in range(3, 13):
    S = switched_Kdd(d, 1); assert is_regular(*S, d)
    cS = cdf(dist_dp(*S)); cK = cdf(dist_dp(*K(d)))
    ok0 = cS[0] == 3 * 2**(d - 1) + 1
    ok1 = cS[1] == 2**(d + 1) + d * d + 4 * d - 9
    okK = cK[0] == 2**(d + 1) - 1 and cK[1] == 2**(d + 1) - 1 + d * d
    print(f"d={d:2d}: i0(S)={cS[0]} {ok0}  i1(S)={cS[1]} {ok1}  i1(K)={cK[1]} {okK}  diff={cS[1]-cK[1]} (4d-8={4*d-8})")
    assert ok0 and ok1 and okK and cS[1] - cK[1] == 4 * d - 8
print()
# several copies, t = 1, exact via product formula and via brute force where feasible
from fractions import Fraction
def pred_diff(d, m):
    i0K, i1K = 2**(d+1)-1, 2**(d+1)-1+d*d
    i0S, i1S = 3*2**(d-1)+1, 2**(d+1)+d*d+4*d-9
    H0, H1 = i0K**(m-1), i0K**(m-1) + (m-1)*d*d*i0K**(m-2) if m >= 2 else 0
    if m == 1: H0, H1 = 1, 1
    # i_1(G u H) = i_1(G) i_0(H) + i_0(G) (i_1(H) - i_0(H))
    g = i1S*H0 + i0S*(H1-H0); k = i1K*H0 + i0K*(H1-H0)
    return g - k
for d in range(3, 16):
    ms = [m for m in range(1, 12) if pred_diff(d, m) > 0]
    print(f"d={d:2d}: S_d + (m-1)K_dd beats m K_dd at t=1 exactly for m in {ms}")
# brute-force cross-check of the union formula for small cases
for d, m in [(3, 2), (3, 3), (4, 2), (4, 3), (5, 2)]:
    n = 2*d*m
    if n > 22: continue
    G = disjoint_union(switched_Kdd(d, 1), *[K(d)]*(m-1)); H = disjoint_union(*[K(d)]*m)
    diff = cdf(dist_dp(*G))[1] - cdf(dist_dp(*H))[1]
    print(f"  brute d={d} m={m}: diff={diff} predicted={pred_diff(d, m)}"); assert diff == pred_diff(d, m)
