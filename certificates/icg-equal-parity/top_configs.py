"""Print the top-k configurations (Y_ab=-1) with exact margins target-G, for given shape and (p,q)."""
import sys
from fractions import Fraction as Fr
from core import T, target, Gval, all_sign_matrices
def show(a,b,p,q,k=8):
    M=T(a,p); N=T(b,q); tgt=target(a,b,p,q)
    res=[]
    for Y in all_sign_matrices(a,b):
        g=Gval(Y,p,q,M,N); res.append((tgt-g,[r[:] for r in Y]))
    res.sort(key=lambda t:t[0])
    print(f"== a={a} b={b} p={p} q={q} target={tgt} ({float(tgt):.4f})")
    for gap,Y in res[:k]:
        print(f"   gap={float(gap):12.6f} rel={float(gap/tgt):.3e}  Y={'/'.join(''.join('+' if v>0 else '-' for v in r) for r in Y)}")
if __name__=="__main__":
    for (a,b) in [(2,2),(1,1),(1,3),(3,1)]:
        for (p,q) in [(5,3),(11,3),(40,3),(1000,3),(5,1000),(3,5),(3,40)]:
            show(a,b,p,q,6)
