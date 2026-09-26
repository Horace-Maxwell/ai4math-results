"""Exploration: slack structure of the potential proof for same-parity shapes.
For each sign matrix Y: slack terms sigma_k (k<a) and sigma_a, and need(Y)=2 rho_a rho_b - |Xi|(1+Y00*Yab)."""
from fractions import Fraction as Fr
import itertools
from icg_model import T, dpoly, delta
def Fn(N,w): return sum(abs(sum(N[v][j]*w[j] for j in range(len(w)))) for v in range(len(N)))
def analyse(a,b,p,q):
    N=T(b,q); qb=q**b; Db=Fr(dpoly(b,q),qb)
    mu={-1:Fr(1)}
    for k in range(a): mu[k]=(p-1-mu[k-1])/Fr(p)
    rho_a=Fr(delta(a,p)[a],p**a); rho_b=Fr(delta(b,q)[b],qb)
    worst=None; rows_out=[]
    for bits in itertools.product([1,-1],repeat=(a+1)*(b+1)):
        Y=[list(bits[i*(b+1):(i+1)*(b+1)]) for i in range(a+1)]
        if Y[0][0]!=1: continue  # symmetry Y->-Y
        z={a-1:[Fr(v) for v in Y[a]]}
        for k in range(a-1,-1,-1): z[k-1]=[(z[k][j]+(p-1)*Y[k][j])/p for j in range(b+1)]
        sig=[]
        for k in range(a):
            fk=(Fn(N,[z[k-1][j]-z[k][j] for j in range(b+1)])+mu[k-1]*Fn(N,z[k-1])-mu[k]*Fn(N,z[k]))/qb
            ck=Fr(p-1)*(1+mu[k-1])/p
            sig.append(ck*Db-fk)
        sig.append(mu[a-1]*(Db-Fr(Fn(N,Y[a]),qb)))
        # Xi: q-endpoint of zeta_{-1}
        w=z[-1]; xi=w[b]
        for j in range(b-1,-1,-1): xi=(xi+(q-1)*w[j])/q
        need=2*rho_a*rho_b-abs(xi)*(1+Y[0][0]*Y[a][b])
        tot=sum(sig)
        r=(tot-need)
        if worst is None or r<worst[0]: worst=(r,Y,[float(s) for s in sig],float(need),float(xi))
        rows_out.append((r,Y))
    rows_out.sort(key=lambda t:t[0])
    return worst, rows_out[:5], float(2*rho_a*rho_b)
for (a,b,p,q) in [(1,1,5,3),(1,1,5,7),(2,2,5,3),(1,3,5,3),(3,1,5,3),(2,2,7,5)]:
    worst,top,need0=analyse(a,b,p,q)
    print(f"(a,b,p,q)=({a},{b},{p},{q}): min over Y of [total slack - need] = {float(worst[0]):.6f}; 2rho_a rho_b={need0:.4f}")
    for r,Y in top[:4]: print("    ",f"{float(r):.6f}",Y)
