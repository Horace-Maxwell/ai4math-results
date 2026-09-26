"""Does the Theorem-5 stepwise bound f_k <= c_k d_F hold when the PATH side is x=3 and the F-side prime is >= 5?
(transposed use: path over the q=3 side, F = ||T_a(p) .||_1).  Exhaustive over sign matrices for small shapes, exact."""
import itertools, sys
from fractions import Fraction as Fr
from core import T, dfun
def F(N,w): return sum(abs(sum(N[v][j]*w[j] for j in range(len(w)))) for v in range(len(N)))
def worst_step(m, x, a, p):
    # path side: m+1 "rows" (inputs are vectors in R^{a+1}), path base x; F-side T_a(p)
    N=T(a,p); dF=dfun(a,p)
    mu={-1:Fr(1)}
    for k in range(m): mu[k]=(x-1-mu[k-1])/Fr(x)
    worst=Fr(-10**9); arg=None
    for bits in itertools.product([1,-1],repeat=(m+1)*(a+1)):
        rows=[[Fr(bits[i*(a+1)+j]) for j in range(a+1)] for i in range(m+1)]
        zeta={m-1:rows[m]}
        for k in range(m-1,-1,-1): zeta[k-1]=[(zeta[k][j]+(x-1)*rows[k][j])/x for j in range(a+1)]
        for k in range(m):
            fk=F(N,[zeta[k-1][j]-zeta[k][j] for j in range(a+1)])+mu[k-1]*F(N,zeta[k-1])-mu[k]*F(N,zeta[k])
            ck=Fr(x-1)*(1+mu[k-1])/x
            e=fk-ck*dF
            if e>worst: worst=e; arg=(k,[[int(v) for v in r] for r in rows])
    return worst,arg
for (m,a) in [(1,2),(2,2),(3,2),(1,3),(2,3),(3,3),(1,4),(2,4),(4,2)]:
    for p in (5,7,11):
        w,arg=worst_step(m,3,a,p)
        print(f"path x=3 (exp {m}), F-side T_{a}({p}): max_k (f_k - c_k d_F) = {float(w):.6g}  {'OK' if w<=0 else 'FAIL at '+str(arg)}")
        sys.stdout.flush()
