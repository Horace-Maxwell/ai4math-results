"""Test the strengthened corner inequality (Theorem 5') for a+b even:
  sum_{(u,v)!=(a,b)} |Z_uv| + |Z_ab - dA dB Y_ab| <= d_a d_b - dA dB,   Z = T_a(p) Y T_b(q)^T,
where dA = delta_a(p) (last diagonal entry), dB = delta_b(q). Exhaustive over sign matrices (numpy, exact int64)."""
import numpy as np, itertools, sys
from icg_model import T, dpoly, delta
def run(a,b,p,q):
    M=np.array(T(a,p),dtype=np.int64); N=np.array(T(b,q),dtype=np.int64)
    dA=delta(a,p)[a]; dB=delta(b,q)[b]; D=dpoly(a,p)*dpoly(b,q)
    nc=(a+1)*(b+1)
    # Kronecker operator on vec(Y) row-major: Z = M Y N^T -> vec_rm(Z) = (M kron N) vec_rm(Y)
    K=np.kron(M,N)
    best=None; arg=[]
    B=1<<nc
    chunk=1<<min(nc,16)
    for start in range(0,B,chunk):
        idx=np.arange(start,min(B,start+chunk),dtype=np.int64)
        Y=((idx[:,None]>>np.arange(nc))&1)*2-1   # rows: sign vectors (row-major cells)
        Z=Y@K.T
        corner=a*(b+1)+b
        val=np.abs(Z).sum(1)-np.abs(Z[:,corner])+np.abs(Z[:,corner]-dA*dB*Y[:,corner])
        m=val.max()
        if best is None or m>best: best=m; arg=list(idx[val==m][:4])
        elif m==best: arg+=list(idx[val==m][:4])
    return best, D-dA*dB, arg
for (a,b) in [(1,1),(2,2),(1,3),(3,1),(3,3),(2,4),(4,2),(1,5),(5,1),(2,1),(1,2),(2,3)]:
    for (p,q) in [(5,3),(3,5),(5,7),(7,3),(7,5),(11,3)]:
        if (a+1)*(b+1)>18: continue
        m,rhs,arg=run(a,b,p,q)
        tag='OK' if m<=rhs else 'FAIL'
        print(f"a={a} b={b} p={p} q={q} max={m} rhs={rhs} {tag} (a+b {'even' if (a+b)%2==0 else 'odd'}) argmax={arg[:3]}")
