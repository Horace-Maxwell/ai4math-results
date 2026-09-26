"""Classification of the admissible last columns g (g_a = -1) for a = 3, 4 by the sign of Delta(g) - 2 delta_a(p),
at sample primes p (Delta depends only on p). Also provides T_k(x) and mv() for prop_reduction_spot.py."""
from fractions import Fraction as F
import itertools
def T(k, x):
    t = [[F(0)]*(k+1) for _ in range(k+1)]
    for i in range(k):
        for j in range(k):
            if i+j <= k-2: t[i][j] = F(0)
            elif i+j == k-1: t[i][j] = -x**(k-1)*(x-1)
            else: t[i][j] = x**(2*k-i-j-2)*(x-1)**2
    for i in range(k):
        t[i][k] = t[k][i] = x**(k-i-1)*(x-1)
    t[k][k] = F(1)
    return t
def mv(M, v): return [sum(a*b for a, b in zip(r, v)) for r in M]
if __name__ == '__main__':
    for a in (3, 4):
        for p in (F(3), F(5), F(7), F(101)):
            M = T(a, p); sa = [(-1)**i for i in range(a+1)]
            al = mv(M, sa); d = sum(abs(x) for x in al); de = al[a]
            anti = tuple(-((-1)**a)*v for v in sa)
            gp = tuple(((-1)**a)*v for v in sa[:-1]) + (((-1)**a)*sa[-1]-2,)
            cheap = []; big = 0; eq = []
            for g in itertools.product([1, -1], repeat=a+1):
                if g[a] != -1 or g == anti: continue
                Dg = d - sum(abs(x) for x in mv(M, g))
                if g == gp:
                    assert Dg == 2*de; continue
                if Dg < 2*de: cheap.append(g)
                elif Dg > 2*de: big += 1
                else: eq.append(g)
            print(f"a={a} p={p}: cheap={cheap} big={big} equal={eq} g+={gp}")
