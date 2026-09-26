"""Split by Y_00: case (i) Y_00=+1 (Z_ab>0): need ||Z||_1 <= dd-2dd'; case (ii) Y_00=-1: need ||Z||_1-2|Z_ab| <= dd-2dd'.
Report min relative margins per case and the near-tight configurations (float64, exhaustive)."""
import numpy as np
from core import T, dfun, delta_last
def fmt(row,a,b): return '/'.join(''.join('+' if row[i*(b+1)+j]>0 else '-' for j in range(b+1)) for i in range(a+1))
def run(a,b,p,q,k=4):
    M=np.array([[float(v) for v in r] for r in T(a,p)]); N=np.array([[float(v) for v in r] for r in T(b,q)])
    K=np.kron(M,N); nc=(a+1)*(b+1); free=nc-1
    idx=np.arange(1<<free,dtype=np.int64)
    Yf=((idx[:,None]>>np.arange(free))&1)*2-1
    Y=np.concatenate([Yf,-np.ones((len(idx),1),dtype=np.int64)],1)
    Z=Y@K.T; H=np.abs(Z).sum(1); c=Z[:,-1]
    dd=float(dfun(a,p)*dfun(b,q)); de=float(delta_last(a,p)*delta_last(b,q)); tgt=dd-2*de
    out=[]
    for case,mask,val in [("i (Y00=+1)",Y[:,0]==1,H),("ii (Y00=-1)",Y[:,0]==-1,H-2*np.abs(c))]:
        m=tgt-val[mask]; Ys=Y[mask]; o=np.argsort(m)[:k]
        out.append((case,[(m[t]/tgt,fmt(Ys[t],a,b)) for t in o]))
    return out
for (a,b) in [(1,1),(2,2),(1,3),(3,1),(3,3),(2,4),(4,2)]:
    for (p,q) in [(5,3),(3,5),(40,3),(7,5)]:
        for case,lst in run(a,b,p,q):
            print(f"a={a} b={b} p={p} q={q} case {case}: "+"  ".join(f"{r:.4f}:{s}" for r,s in lst))
