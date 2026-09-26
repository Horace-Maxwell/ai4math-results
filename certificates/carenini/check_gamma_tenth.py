"""Verify the reviewer's remark: at fixed gamma = 1/10 < 1/8, k*H_d (+ r*K_dd) vs m*K_dd for moderately large n."""
from Hd_poly import poly_H, poly_2K
from ecount import dist_dp, K
def to_list(P):
    L = [0]*(max(P)+1)
    for s, c in P.items(): L[s] += c
    return L
def pmul(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b): out[i+j] += x*y
    return out
def ppow(a, k):
    r = [1]; base = a
    while k:
        if k & 1: r = pmul(r, base)
        base = pmul(base, base); k >>= 1
    return r
for d in (2, 3):
    PH = to_list(poly_H(d)); PK = [int(x) for x in dist_dp(*K(d))]
    res = []
    for n in range(4*d, 4*d*60 + 1, 2*d):
        m = n // (2*d); k, r = divmod(m, 2)
        t = (d*n) // 10          # floor(gamma d n), gamma = 1/10
        G = pmul(ppow(PH, k), ppow(PK, r)); M = ppow(PK, m)
        a, b = sum(G[:t+1]), sum(M[:t+1])
        res.append((n, 'H' if a > b else ('=' if a == b else 'K')))
    wins = [n for n, w in res if w == 'H']
    print(f"d={d}, gamma=1/10: competitor k*H_d+r*K wins at {len(wins)} of {len(res)} n in [{4*d},{4*d*60}]; largest winning n = {max(wins) if wins else None}; first 12 winners {wins[:12]}")
