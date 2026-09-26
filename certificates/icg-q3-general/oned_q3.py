"""1D q-side facts at x=3: inf->1 norm of T_b(3) over sign vectors; eigen-structure of Delta +- T."""
import numpy as np
from itertools import product
from icg_model import T, delta, dpoly
x=3
for b in range(1,16,2):
    N=np.array(T(b,x),dtype=float); D=np.diag(delta(b,x))
    # enumerate sign vectors y (fix y0=+1)
    best=[];
    Ni=np.array(T(b,x),dtype=object)
    vals={}
    for bits in product([1,-1],repeat=b):
        y=np.array((1,)+bits,dtype=np.int64)
        v=int(np.abs(np.array(T(b,x),dtype=np.int64)@y).sum())
        vals[tuple(y)]=v
    srt=sorted(vals.items(),key=lambda kv:-kv[1])
    s=tuple((-1)**i for i in range(b+1))
    ep=np.linalg.eigvalsh(D+N); em=np.linalg.eigvalsh(D-N)
    print(f"b={b} d_b(3)={dpoly(b,3)} max={srt[0][1]} argmax_is_s={srt[0][0]==s} second={srt[1][1]} gap={srt[0][1]-srt[1][1]} secondarg={srt[1][0]}")
    print("   eig(D+T) min", ep[:2].round(4), " eig(D-T) min", em[:2].round(4))
