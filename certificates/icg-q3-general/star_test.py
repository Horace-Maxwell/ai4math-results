"""Test the local potential inequality (star):
  P*F(y - z) + mu*F(z + P*y) - (P - mu)*F(z) <= P*(1+mu)*d_b
for F(w)=||T_b(3) w||_1, y vertex, z in corner region y'*t, t in [(p-2)/p,1]^{b+1}, mu in [(p-2)/p,1]."""
import numpy as np, itertools, sys
from icg_model import T, dpoly
rng=np.random.default_rng(1)
def F(N,w): return np.abs(N@w).sum()
for b in (1,3,5):
    N=np.array(T(b,3),dtype=float); db=dpoly(b,3)
    verts=[np.array(v,dtype=float) for v in itertools.product([1,-1],repeat=b+1)]
    for p in (5,7,11):
        P=p-1; worst=-1e18; arg=None
        mus=[(p-2)/p,1.0,(p-1)/(p+1)]
        for y in verts[:len(verts)//2]:   # symmetry y->-y
            for yp in verts:
                # corner samples
                for trial in range(60):
                    if trial==0: t=np.ones(b+1)
                    elif trial==1: t=np.full(b+1,(p-2)/p)
                    else: t=rng.uniform((p-2)/p,1,b+1)
                    z=yp*t
                    for mu in mus:
                        lhs=P*F(N,y-z)+mu*F(N,z+P*y)-(P-mu)*F(N,z)
                        exc=lhs-P*(1+mu)*db
                        if exc>worst: worst=exc; arg=(y,yp,t.round(3),mu)
        print(f"b={b} p={p} worst excess {worst:.4f} (relative {worst/(P*2*db):.2e}) at y={arg[0]} yp={arg[1]} t={arg[2]} mu={arg[3]:.3f}")
