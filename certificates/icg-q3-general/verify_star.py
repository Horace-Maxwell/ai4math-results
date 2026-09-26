"""Exact (Fraction) verification of every step of the potential proof.
(V1) scalar path identity ||T_m(x) w||_1 = x^m (|z_{-1}| + sum_k |z_{k-1}-z_k|) for real w.
(V2) vertex slack identity: F(y)/q^b = sum_j c^q_j + mu^q_{b-1} - sum_{j in NA(y)} 2 mu^q_j |xi_j(y)|.
(V3) per-cell bounds and the local inequality (star) for random y, random zeta in the cube,
     random P>=4, mu in [3/5,1] (plus boundary values), and adversarial coordinate search.
"""
from fractions import Fraction as Fr
import random, itertools, sys, time
from icg_model import T, dpoly

def path(w, x):
    """z[k] for k=-1..m-1 (dict) : z[m-1]=w[m], z[k-1]=(z[k]+(x-1)w[k])/x"""
    m=len(w)-1; z={m-1:Fr(w[m])}
    for k in range(m-1,-1,-1): z[k-1]=(z[k]+(x-1)*w[k])/x
    return z
def terms(w,x):
    """tau_{-1}=z_{-1}, tau_k=z_{k-1}-z_k (k=0..m-1)"""
    z=path(w,x); m=len(w)-1
    return [z[-1]]+[z[k-1]-z[k] for k in range(m)]
def Fnorm(Tm,w): return sum(abs(sum(Tm[v][j]*w[j] for j in range(len(w)))) for v in range(len(Tm)))
def mus(m,x):
    mu={-1:Fr(1)}
    for k in range(0,m): mu[k]=(x-1-mu[k-1])/Fr(x)
    return mu
random.seed(12345)
t0=time.time()
# V1
for m in range(1,9):
    for x in (Fr(3),Fr(5),Fr(7),Fr(11,2),Fr(13)):
        Tm=T(m,x)
        for it in range(40):
            w=[Fr(random.randint(-50,50),random.randint(1,20)) for _ in range(m+1)]
            lhs=Fnorm(Tm,w); rhs=x**m*sum(abs(t) for t in terms(w,x))
            assert lhs==rhs,(m,x,w)
print("V1 ok", round(time.time()-t0,1))
# V2 (q=3, all vertices, b<=12)
q=Fr(3)
for b in range(1,13):
    Tb=T(b,q); mu=mus(b,q); db=dpoly(b,3)
    cq=[(q-1)*(1+mu[j-1])/q for j in range(b)]
    base=sum(cq)+mu[b-1]
    assert base*q**b==db,(b,base*q**b,db)
    for y in itertools.product([1,-1],repeat=b+1):
        z=path(y,q)
        NA=[j for j in range(b) if y[j]==y[j+1]]
        pred=base-sum(2*mu[j]*abs(z[j]) for j in NA)
        assert Fnorm(Tb,y)==pred*q**b,(b,y)
        # also: alternating cells / NA cells magnitude formulas
        for j in range(b):
            A=(q-1)/q*(y[j]-z[j])
            assert abs(A)==(q-1)/q*((1-abs(z[j])) if j in NA else (1+abs(z[j])))
            if j<b-1: assert abs(z[j])>=(q-2)/q
print("V2 ok (b<=12, all vertices)", round(time.time()-t0,1))
# V3 local inequality (star)
def star_excess(Tb,db,y,zeta,P,mu):
    ym=[Fr(v) for v in y]
    lhs=P*Fnorm(Tb,[ym[j]-zeta[j] for j in range(len(y))])+mu*Fnorm(Tb,[zeta[j]+P*ym[j] for j in range(len(y))])-(P-mu)*Fnorm(Tb,zeta)
    return lhs-P*(1+mu)*db
def rand_fr(lo,hi,den=97):
    return Fr(lo)+(Fr(hi)-Fr(lo))*Fr(random.randint(0,den),den)
worst_overall=None
for b in range(1,10):
    Tb=T(b,q); db=dpoly(b,3); mu_q=mus(b,q)
    worst=None; cnt=0
    verts=list(itertools.product([1,-1],repeat=b+1))
    ntr=4000 if b<=5 else 1500
    for it in range(ntr):
        y=random.choice(verts)
        mode=random.random()
        if mode<0.3: zeta=[Fr(random.choice([-1,1])) for _ in range(b+1)]
        elif mode<0.6: zeta=[rand_fr(-1,1) for _ in range(b+1)]
        else:
            yp=random.choice(verts); zeta=[yp[j]*rand_fr(Fr(1,2),1) for j in range(b+1)]
        P=random.choice([Fr(4),Fr(6),Fr(10),rand_fr(4,20)])
        mu=random.choice([Fr(3,5),Fr(1),rand_fr(Fr(3,5),1)])
        e=star_excess(Tb,db,y,zeta,P,mu); cnt+=1
        # per-cell bound check
        A=terms(y,q); B=terms(zeta,q); zy=path(y,q)
        NA=[j for j in range(b) if y[j]==y[j+1]]
        for idx in range(b+1):
            j=idx-1
            a_,b_=A[idx],B[idx]
            g=P*abs(a_-b_)+mu*abs(b_+P*a_)-(P-mu)*abs(b_)
            h=g-P*(1+mu)*abs(a_)
            if j>=0 and j in NA:
                assert h< 2*P*(1+mu)*mu_q[j]*abs(zy[j]), (b,y,zeta,j)
            else:
                assert h<=0,(b,y,zeta,j,h)
        if not (y==tuple((-1)**i for i in range(b+1)) or y==tuple(-(-1)**i for i in range(b+1))):
            assert e<0,(b,y,zeta,P,mu,e)
        assert e<=0,(b,y,zeta,P,mu,e)
        worst=e if worst is None or e>worst else worst
    print(f"V3 b={b}: {cnt} exact random tests, max excess {float(worst):.4g}", round(time.time()-t0,1))
# adversarial: coordinate ascent on zeta over a grid, P=4, mu in {3/5,1}, all vertices y (b<=5)
for b in range(1,6):
    Tb=T(b,q); db=dpoly(b,3)
    grid=[Fr(i,24) for i in range(-24,25)]
    best=None
    for y in itertools.product([1,-1],repeat=b+1):
        for mu in (Fr(3,5),Fr(1)):
            for rs in range(6):
                zeta=[random.choice(grid) for _ in range(b+1)]
                cur=star_excess(Tb,db,y,zeta,Fr(4),mu)
                improved=True
                while improved:
                    improved=False
                    for j in range(b+1):
                        for g in grid:
                            z2=zeta[:]; z2[j]=g
                            v=star_excess(Tb,db,y,z2,Fr(4),mu)
                            if v>cur: cur=v; zeta=z2; improved=True
                best=cur if best is None or cur>best else best
                assert cur<=0
    print(f"adversarial b={b}: max excess found {float(best):.4g}", round(time.time()-t0,1))
