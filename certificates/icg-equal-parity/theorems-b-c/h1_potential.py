"""Test the corner potential for H1 along the p-path (rows):
Pi_k(zeta) = mu_k F(zeta) - 2 lam_k |(N zeta)_b|,  lam_k = mu_{a-1}/mu_{a-2-k}  (lam_{-1}=1, lam_{a-1}=mu_{a-1}).
Step k: S_k = F(z'-z) + Pi_{k-1}(z') - Pi_k(z) <= c_k D, z' = (z + P y)/p.   Exact (Fractions), all sign matrices."""
import sys, itertools
from fractions import Fraction as Fr
from core import T, dfun, mus
def matvec(A, x): return [sum(A[i][j] * x[j] for j in range(len(x))) for i in range(len(A))]
def run(a, b, p, q):
    p = Fr(p); q = Fr(q); P = p - 1
    N = T(b, q); D = dfun(b, q)
    mu = mus(a, p)                      # mu[-1..a-1]
    lam = {k: mu[a - 1] / mu[a - 2 - k] for k in range(-1, a)}
    c = {k: P * (1 + mu[k - 1]) / p for k in range(a)}
    F = lambda z: sum(abs(t) for t in matvec(N, z))
    cor = lambda z: abs(matvec(N, z)[b])
    Pi = lambda k, z: mu[k] * F(z) - 2 * lam[k] * cor(z)
    worst = {k: None for k in range(a)}
    signs = list(itertools.product([1, -1], repeat=b + 1))
    # enumerate all row sign vectors bottom-up; states zeta_k reachable
    def rec(k, z, rows):
        # z = zeta_k ; choose y = row k
        if k < 0: return
        for y in signs:
            zp = [(z[j] + P * y[j]) / p for j in range(b + 1)]
            S = F([zp[j] - z[j] for j in range(b + 1)]) + Pi(k - 1, zp) - Pi(k, z) - c[k] * D
            if worst[k] is None or S > worst[k][0]:
                worst[k] = (S, rows + [y])
            rec(k - 1, zp, rows + [y])
    for w in signs:
        rec(a - 1, [Fr(t) for t in w], [w])
    out = ', '.join(f"k={k}: max(S_k - c_k D)={float(worst[k][0]):+.5g}" + ("" if worst[k][0] <= 0 else f" at rows(bottom-up)={worst[k][1]}") for k in range(a))
    print(f"a={a} b={b} p={p} q={q}: {out}")
    sys.stdout.flush()
if __name__ == "__main__":
    for (a, b) in [(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3)]:
        for (p, q) in [(5, 3), (3, 5), (7, 3), (5, 7), (11, 3), (3, 11)]:
            run(a, b, p, q)
