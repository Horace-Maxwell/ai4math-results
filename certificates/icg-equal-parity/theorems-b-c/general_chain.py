"""FD2 analogue for general a: for each 'cheap' last column g (g[a] = -1, g != anti last column, Delta(g) < 2 delta_a),
the g-chain c_j = (-1)^{b-j} g (j < b) and the first deviation J' from it (exact state (-1)^{b-1-J'} mu_{b-2-J'} g).
Check: chain cost + s_{J'} > (2 delta_a - Delta(g)) rho for every deviation, and the full chain (+kappa) pays."""
import itertools, sys
from fractions import Fraction as Fr
from core import T, mus, dfun, delta_last, path
from general_a import surplus, mv
def run(a, p, q, bs):
    p = Fr(p); q = Fr(q); Q = q - 1
    M = T(a, p); Dp = dfun(a, p); da = delta_last(a, p)
    sa = [(-1) ** i for i in range(a + 1)]
    cols = list(itertools.product([1, -1], repeat=a + 1))
    res = {}
    for b in bs:
        if (a + b) % 2: continue
        anti_last = [-(-1) ** b * x for x in sa]
        mu = mus(b + 2, q); rho = mu[b - 1]
        for g in cols:
            if g[a] != -1 or list(g) == anti_last: continue
            Dg = Dp - sum(abs(x) for x in mv(M, g))
            if Dg >= 2 * da: continue
            extra = (2 * da - Dg) * rho
            chain = Fr(0); worst = None
            for Jp in range(b - 1, -2, -1):
                if Jp == -1:
                    # full chain: columns c_j = (-1)^{b-j} g for all j <= b; add kappa
                    Y = [[(-1) ** (b - j) * g[i] for j in range(b + 1)] for i in range(a + 1)]
                    r_last = [sum(M[a][k] * Y[k][j] for k in range(a + 1)) for j in range(b + 1)]
                    kap = 2 * max(Fr(0), -path(r_last, q)[-1])
                    rr = (chain + kap) / extra
                    if worst is None or rr < worst[0]: worst = (rr, 'full', b)
                    break
                sig = (-1) ** (b - 1 - Jp)
                zeta = [sig * mu[b - 2 - Jp] * x for x in g]
                cont = [-sig * x for x in g]
                for c in cols:
                    if list(c) == cont: continue
                    s = surplus(M, Dp, Q, q, mu[Jp - 1], c, zeta)
                    rr = (chain + s) / extra
                    if worst is None or rr < worst[0]: worst = (rr, c, Jp, b)
                chain += surplus(M, Dp, Q, q, mu[Jp - 1], cont, zeta)
            key = tuple(g)
            if key not in res or worst[0] < res[key][0]: res[key] = worst
    for g, w in res.items():
        print(f"  a={a} p={p} q={q} g={g}: min (chain+dev)/need_extra = {float(w[0]):.4f} at {w[1:]}{'  <-- FAILS' if w[0] <= 1 else ''}")
    sys.stdout.flush()
if __name__ == "__main__":
    for a in [2, 3, 4]:
        bs = [b for b in range(1, 11) if (a + b) % 2 == 0]
        for (p, q) in [(5, 3), (7, 3), (3, 5), (3, 7), (3, 101), (101, 3), (5, 7)]:
            run(a, p, q, bs)
