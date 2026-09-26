"""Generating polynomial of e_H(A) for H_d (two K_{d,d} joined by a switch) via conditioning on
the membership (alpha,beta) of the switched vertices x,y in each block."""
from math import comb
def W(d, a, b):
    # sum over a' subset of X-x, b' subset of Y-y of z^{(a'+a)(b'+b) - a*b}
    P = {}
    for i in range(d):
        for j in range(d):
            s = (i + a) * (j + b) - a * b
            P[s] = P.get(s, 0) + comb(d-1, i) * comb(d-1, j)
    return P
def mul(P, Q, shift=0):
    R = {}
    for s, c in P.items():
        for u, e in Q.items():
            R[s+u+shift] = R.get(s+u+shift, 0) + c*e
    return R
def add(P, Q):
    R = dict(P)
    for s, c in Q.items(): R[s] = R.get(s, 0) + c
    return R
def poly_H(d):
    tot = {}
    for a1 in (0,1):
        for b1 in (0,1):
            for a2 in (0,1):
                for b2 in (0,1):
                    tot = add(tot, mul(W(d,a1,b1), W(d,a2,b2), a1*b2 + a2*b1))
    return tot
def poly_2K(d):
    tot = {}
    for a1 in (0,1):
        for b1 in (0,1):
            for a2 in (0,1):
                for b2 in (0,1):
                    tot = add(tot, mul(W(d,a1,b1), W(d,a2,b2), a1*b1 + a2*b2))
    return tot
def cum(P, t): return sum(c for s, c in P.items() if s <= t)
if __name__ == '__main__':
    from ecount import dist_dp, disjoint_union, K, cdf
    # cross-check with brute force for d=2,3,4
    import small_numbers  # noqa (prints)
    for d in range(2, 21):
        PH, PK = poly_H(d), poly_2K(d)
        assert sum(PH.values()) == 4**(2*d) == sum(PK.values())
        print(f"d={d:2d}: i_0(H)={cum(PH,0)} i_0(2K)={cum(PK,0)}  i_1(H)-i_1(2K) = {cum(PH,1)-cum(PK,1)}")
