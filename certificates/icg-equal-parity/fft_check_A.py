"""Independent spectral check of Corollary A: for n = p q^m (m odd) compute the energy of ICG_n(D) for ALL nonempty sets D of proper
divisors from the eigenvalues of the actual circulant adjacency matrix (FFT of the first row, float64), and compare the maximum and
the maximisers with the closed form 1/2[n + (3p-4) d_m(q)] - (p-2) delta_m(q). Also dense eigvalsh for the two maximisers when n is small."""
import numpy as np, itertools, math, sys
from core import dfun, delta_last
def divisors(n): return [d for d in range(1,n) if n%d==0]
def energy(n, D, g):
    c=np.isin(g, list(D)).astype(float); c[0]=0.0
    lam=np.fft.fft(c).real
    return np.abs(lam).sum()
for (p,q,m) in [(5,3,1),(5,3,3),(3,5,3),(7,3,3),(3,7,3),(5,3,5),(11,3,3),(3,5,5),(7,5,3),(13,3,3)]:
    n=p*q**m; g=np.array([math.gcd(j,n) for j in range(n)])
    divs=divisors(n)
    best=-1; arg=[]
    for r in range(1,len(divs)+1):
        for D in itertools.combinations(divs,r):
            e=energy(n,D,g)
            if e>best+1e-6: best=e; arg=[D]
            elif abs(e-best)<=1e-6: arg.append(D)
    formula=float(n+ (3*p-4)*dfun(m,q))/2 - float((p-2)*delta_last(m,q))
    anti=tuple(sorted(p**i*q**j for i in range(2) for j in range(m+1) if (i+j)%2==1))
    trunc=tuple(sorted(p**i*q**j for i in range(2) for j in range(m+1) if (i+j)%2==0 and p**i*q**j!=n))
    ok = abs(best-formula)<1e-6*max(1,formula) and sorted(arg)==sorted([anti,trunc])
    dense=''
    if n<=700:
        for D in (anti,trunc):
            A=np.array([[1.0 if (i!=j and math.gcd((j-i)%n,n) in D) else 0.0 for j in range(n)] for i in range(n)])
            ev=np.linalg.eigvalsh(A); dense+=f" dense({len(D)} el)={np.abs(ev).sum():.6f}"
    print(f"n={n}={p}*{q}^{m}: #sets={2**len(divs)-1} max={best:.6f} formula={formula:.6f} maximisers={arg} {'OK' if ok else 'MISMATCH'}{dense}")
    sys.stdout.flush()
