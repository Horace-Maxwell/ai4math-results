"""Test candidate p-side inequalities (exact integers) for small a, p."""
import numpy as np
from itertools import product
from icg_model import T, delta, dpoly
def l1(v): return int(np.abs(v).sum())
for a in (2,4,6):
    for p in (3,5,7,11):
        M=np.array(T(a,p),dtype=np.int64); d=dpoly(a,p); D=np.array(delta(a,p),dtype=np.int64)
        signs=[np.array(s,dtype=np.int64) for s in product([1,-1],repeat=a+1)]
        MY={tuple(y):M@y for y in signs}
        # L1: 2||M g_D|| + ||M g_A|| <= 2 d  for all partitions and signs g
        worst1=-10**30; arg1=None
        for g in signs:
            for mask in range(1<<(a+1)):
                Dm=np.array([(mask>>i)&1 for i in range(a+1)])
                val=2*l1(M@(g*Dm))+l1(M@(g*(1-Dm)))
                if val-2*d>worst1: worst1=val-2*d; arg1=(tuple(g),tuple(Dm))
        # L2: ||M(y-y')|| + y^T M y' <= d
        worst2=-10**30; arg2=None
        for y in signs:
            for y2 in signs:
                val=l1(M@(y-y2))+int(y@M@y2)
                if val-d>worst2: worst2=val-d; arg2=(tuple(y),tuple(y2))
        # additive ternary: ||M g_D|| <= Delta(D)
        worst3=-10**30
        for g in signs:
            for mask in range(1,1<<(a+1)):
                Dm=np.array([(mask>>i)&1 for i in range(a+1)])
                worst3=max(worst3,l1(M@(g*Dm))-int(D@Dm))
        print(f"a={a} p={p} d={d}  L1 max excess={worst1} at {arg1};  L2 max excess={worst2} at {arg2}; additive-ternary max excess={worst3}")
