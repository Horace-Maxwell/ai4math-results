"""Lemma 4 random exact tests for larger b (q=3), P=4, mu in {3/5,1}: near-extremal y (few flips of s_b)
and zeta near -y or random corners."""
from fractions import Fraction as Fr
import random, time
from icg_model import T, dpoly
def Fn(N,w): return sum(abs(sum(N[v][j]*w[j] for j in range(len(w)))) for v in range(len(N)))
random.seed(99); t0=time.time()
q=3
for b in (11,15,20):
    N=T(b,q); db=dpoly(b,q); worst=None
    s=[(-1)**j for j in range(b+1)]
    for it in range(150):
        y=s[:]
        for _ in range(random.choice([0,1,1,2,3])):
            j=random.randrange(b+1); y[j]=-y[j]
        mode=random.random()
        if mode<0.4: zeta=[-yj*Fr(random.randint(60,100),100) for yj in y]
        elif mode<0.7:
            yp=[random.choice([1,-1]) for _ in range(b+1)]; zeta=[v*Fr(random.randint(60,100),100) for v in yp]
        else: zeta=[Fr(random.randint(-100,100),100) for _ in range(b+1)]
        for P in (Fr(4),Fr(6)):
            for mu in (Fr(3,5),Fr(1)):
                lhs=P*Fn(N,[y[j]-zeta[j] for j in range(b+1)])+mu*Fn(N,[zeta[j]+P*y[j] for j in range(b+1)])-(P-mu)*Fn(N,zeta)
                e=lhs-P*(1+mu)*db
                assert e<=0,(b,y,zeta,P,mu)
                if y!=s and y!=[-v for v in s]: assert e<0
                worst=e if worst is None or e>worst else worst
    print(f"b={b}: 600 exact tests pass, max excess {float(worst):.4g}, {time.time()-t0:.1f}s")
