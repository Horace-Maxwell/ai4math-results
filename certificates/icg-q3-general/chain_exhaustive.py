"""Exhaustive exact check of the potential chain (Theorem 5 proof) over ALL sign matrices for small (a,b),
at the boundary prime p=5 and q=3: every step f_k <= c_k d_b, final bound, and equality set = {+-s s^T}.
Also random large instances (a up to 12, b up to 9)."""
from fractions import Fraction as Fr
import itertools, random, time
from icg_model import T, dpoly
def Fn(N,w): return sum(abs(sum(N[v][j]*w[j] for j in range(len(w)))) for v in range(len(N)))
def chain(Y,a,b,p,N,db,mu):
    rows=[[Fr(x) for x in r] for r in Y]
    z={a-1:rows[a]}
    for k in range(a-1,-1,-1): z[k-1]=[(z[k][j]+(p-1)*rows[k][j])/p for j in range(b+1)]
    ok=True; total=Fr(0)
    for k in range(a):
        fk=Fn(N,[z[k-1][j]-z[k][j] for j in range(b+1)])+mu[k-1]*Fn(N,z[k-1])-mu[k]*Fn(N,z[k])
        ck=Fr(p-1)*(1+mu[k-1])/p
        if fk>ck*db: ok=False
        total+=fk
    total+=mu[a-1]*Fn(N,rows[a])
    return ok,total
t0=time.time()
p,q=5,3
for (a,b) in [(1,1),(2,1),(1,2),(2,2),(3,1),(1,3),(2,3),(3,2),(4,1),(1,4)]:
    N=T(b,q); db=dpoly(b,q)
    mu={-1:Fr(1)}
    for k in range(a): mu[k]=(p-1-mu[k-1])/Fr(p)
    bound=Fr(dpoly(a,p)*db,p**a)
    eq=[]; nall=0
    for bits in itertools.product([1,-1],repeat=(a+1)*(b+1)):
        Y=[list(bits[i*(b+1):(i+1)*(b+1)]) for i in range(a+1)]
        ok,total=chain(Y,a,b,p,N,db,mu); nall+=1
        assert ok and total<=bound,(a,b,Y)
        if total==bound: eq.append(Y)
    s=lambda m:[(-1)**i for i in range(m+1)]
    chk=[[x*y for y in s(b)] for x in s(a)]
    assert sorted(eq)==sorted([chk,[[-v for v in r] for r in chk]]),(a,b,eq)
    print(f"(a,b)=({a},{b}) p=5 q=3: all {nall} sign matrices pass; equality exactly at +-s_a s_b^T", round(time.time()-t0,1))
random.seed(7)
for (a,b) in [(8,5),(12,3),(6,9),(10,7)]:
    for p in (5,7,13):
        N=T(b,q); db=dpoly(b,q)
        mu={-1:Fr(1)}
        for k in range(a): mu[k]=(p-1-mu[k-1])/Fr(p)
        bound=Fr(dpoly(a,p)*db,p**a)
        for it in range(40):
            Y=[[random.choice([1,-1]) for j in range(b+1)] for i in range(a+1)]
            ok,total=chain(Y,a,b,p,N,db,mu)
            assert ok and total<bound
        print(f"random (a,b)=({a},{b}) p={p}: 40 random sign matrices pass (strict)", round(time.time()-t0,1))
