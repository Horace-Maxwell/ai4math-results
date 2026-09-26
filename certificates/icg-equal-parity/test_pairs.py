"""Test (P1) H(Y+)+H(Y-) <= 2dd-2dd' and (P2) G(Y-) <= (H(Y+)+H(Y-))/2 - dd' (exploratory, float64 exhaustive)."""
import numpy as np
from core import T, dfun, delta_last
def run(a,b,p,q):
    M=np.array([[float(v) for v in r] for r in T(a,p)]); N=np.array([[float(v) for v in r] for r in T(b,q)])
    K=np.kron(M,N); nc=(a+1)*(b+1); free=nc-1
    idx=np.arange(1<<free,dtype=np.int64)
    Yf=((idx[:,None]>>np.arange(free))&1)*2-1
    Ym=np.concatenate([Yf,-np.ones((len(idx),1),dtype=np.int64)],1)
    Yp=np.concatenate([Yf,np.ones((len(idx),1),dtype=np.int64)],1)
    Zm=Ym@K.T; Zp=Yp@K.T
    Hm=np.abs(Zm).sum(1); Hp=np.abs(Zp).sum(1)
    G=Hm-np.abs(Zm[:,-1])+Zm[:,-1]
    dd=float(dfun(a,p)*dfun(b,q)); de=float(delta_last(a,p)*delta_last(b,q))
    P1=(Hp+Hm).max()-(2*dd-2*de)
    P2=(G-(Hp+Hm)/2+de).max()
    return P1/dd,P2/dd
for (a,b) in [(1,1),(2,2),(1,3),(3,1),(3,3),(2,4)]:
    for (p,q) in [(5,3),(3,5),(7,5),(11,3)]:
        P1,P2=run(a,b,p,q); print(f"a={a} b={b} p={p} q={q}: max excess P1={P1:+.4f}  P2={P2:+.4f} (relative to dd; <=0 means holds)")
