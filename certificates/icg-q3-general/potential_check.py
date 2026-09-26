"""Exact check of the p-side path identity and potential decomposition.
E(Y)/p^a = F(zeta_{-1}) + sum_k F(zeta_{k-1}-zeta_k),  zeta_{a-1}=row a, zeta_{k-1}=(zeta_k+(p-1) row_k)/p
Potential: mu_{-1}=1, mu_k=(p-1-mu_{k-1})/p; f_k = F(zeta_{k-1}-zeta_k)+mu_{k-1}F(zeta_{k-1})-mu_k F(zeta_k)
Claim(star): f_k <= c_k d_b with c_k=(p-1)(1+mu_{k-1})/p.  Then E <= d_a d_b.
"""
from fractions import Fraction as Fr
import itertools, random, sys
from icg_model import T, dpoly, matmul, transpose
def F(N,w): return sum(abs(sum(N[v][j]*w[j] for j in range(len(w)))) for v in range(len(N)))
def check(a,b,p,q,Y,N=None):
    N=N or T(b,q)
    rows=[list(map(Fr,r)) for r in Y]
    zeta={a-1:rows[a]}
    for k in range(a-1,-1,-1):
        zeta[k-1]=[(zeta[k][j]+(p-1)*rows[k][j])/p for j in range(b+1)]
    Epath=F(N,zeta[-1])+sum(F(N,[zeta[k-1][j]-zeta[k][j] for j in range(b+1)]) for k in range(a))
    M=T(a,p); Z=matmul(matmul(M,Y),transpose(N)); E=sum(abs(v) for r in Z for v in r)
    assert Epath*p**a==E,(Epath*p**a,E)
    mu={-1:Fr(1)}
    for k in range(0,a): mu[k]=(p-1-mu[k-1])/Fr(p)
    db=dpoly(b,q); worst=None; total=Fr(0)
    for k in range(a):
        fk=F(N,[zeta[k-1][j]-zeta[k][j] for j in range(b+1)])+mu[k-1]*F(N,zeta[k-1])-mu[k]*F(N,zeta[k])
        ck=Fr(p-1)*(1+mu[k-1])/p
        exc=fk-ck*db
        worst=exc if worst is None or exc>worst else worst
        total+=fk
    total+=mu[a-1]*F(N,rows[a])
    assert total==Epath
    # consistency: sum c_k d_b + mu_{a-1} d_b == d_a d_b / p^a
    sc=sum(Fr(p-1)*(1+mu[k-1])/p for k in range(a))+mu[a-1]
    assert sc*p**a==dpoly(a,p),(sc*p**a,dpoly(a,p))
    return worst
random.seed(0)
for (a,b) in [(2,1),(4,1),(2,3),(3,3),(4,3),(6,3),(2,5),(4,5),(5,2),(3,1)]:
    for p in (5,7,3):
        worst=Fr(-10**9)
        nrand=3000
        for it in range(nrand):
            Y=[[random.choice([1,-1]) for j in range(b+1)] for i in range(a+1)]
            w=check(a,b,p,3,Y)
            worst=max(worst,w)
        print(f"a={a} b={b} p={p}: max over random Y of max_k (f_k - c_k d_b) = {float(worst):.6g}")
