"""Independent cross-check: energies of actual circulant adjacency matrices (FFT of first row),
compared with the exact model, for n = p^a * 3^b small. Floating point; diagnostic only."""
import numpy as np, itertools, time
from icg_model import energy, T, X_to_mask
from math import gcd
def divisors(n): return [d for d in range(1,n+1) if n%d==0]
for (p,a,b) in [(5,2,1),(7,2,1),(5,2,3),(5,4,1),(11,2,1),(5,2,5)]:
    n=p**a*3**b
    t0=time.time()
    props=[(i,j) for i in range(a+1) for j in range(b+1) if (i,j)!=(a,b)]
    g=np.array([gcd(k,n) for k in range(n)])
    ind={ (i,j): (g==p**i*3**j).astype(float) for (i,j) in props}
    M=T(a,p); N=T(b,3)
    best=(-1,None); maxdiff=0.0
    for mask in range(1,1<<len(props)):
        row=np.zeros(n)
        X=[[0]*(b+1) for _ in range(a+1)]
        for t,(i,j) in enumerate(props):
            if mask>>t&1: row+=ind[(i,j)]; X[i][j]=1
        ev=np.fft.fft(row).real   # symmetric circulant -> real eigenvalues
        Ef=np.abs(ev).sum()
        Ee=energy(X,p,3,a,b,M,N)
        maxdiff=max(maxdiff,abs(Ef-Ee))
        if Ee>best[0]: best=(Ee,[r[:] for r in X])
    chk=[[1 if (i+j)%2==0 else 0 for j in range(b+1)] for i in range(a+1)]
    print(f"n={n} (p={p},a={a},b={b}): {(1<<len(props))-1} sets, max |FFT energy - exact model| = {maxdiff:.2e}, argmax is checkerboard: {best[1]==chk}, Emax={best[0]}, {time.time()-t0:.1f}s")
