"""Column-path surplus decomposition for shape (2,b), exact Fractions.
Theta/q^b - G/q^b = sum_{j<b} s_j + rho*Delta(c_b) + kappa - 2 delta_p rho.
Types: A=(1,-1,1) B=(1,1,-1) C=(1,-1,-1) E=(1,1,1) (times sign eps = u_j)."""
import itertools, sys
from fractions import Fraction as Fr
from core import T, dfun, delta_last, path, mus

def hfun(Q, mu, A, B):
    return Q * abs(A - B) + mu * abs(B + Q * A) - (Q - mu) * abs(B) - Q * (1 + mu) * abs(A)

def ctype(c):
    e = c[0]; t = tuple(e * x for x in c)
    return {(1, -1, 1): 'A', (1, 1, -1): 'B', (1, -1, -1): 'C', (1, 1, 1): 'E'}[t], e

def decomp(Y, p, q, M=None, muq=None):
    """Y: list of 3 rows (u,v,w). returns dict."""
    b = len(Y[0]) - 1
    p = Fr(p); q = Fr(q); Q = q - 1
    M = M or T(2, p); muq = muq or mus(b, q)
    rho = muq[b - 1]
    chat = {j: Q * (1 + muq[j - 1]) / q for j in range(b)}; chat[b] = rho
    Dp = dfun(2, p); dp = delta_last(2, p)
    cols = [[Y[i][j] for i in range(3)] for j in range(b + 1)]
    r = [[sum(M[i][k] * cols[j][k] for k in range(3)) for j in range(b + 1)] for i in range(3)]
    z = [path(r[i], q) for i in range(3)]
    Fp = [sum(abs(r[i][j]) for i in range(3)) for j in range(b + 1)]
    s = []
    cells = []
    for j in range(b):
        cj = [hfun(Q, muq[j - 1], r[i][j], z[i][j]) / q for i in range(3)]
        cells.append(cj)
        s.append(chat[j] * (Dp - Fp[j]) - sum(cj))
    sb = rho * (Dp - Fp[b])
    kappa = 2 * max(Fr(0), -z[2][-1])
    need = 2 * dp * rho
    total = sum(s) + sb + kappa - need
    return dict(s=s, sb=sb, kappa=kappa, need=need, total=total, types=[ctype(c) for c in cols], cells=cells, rho=rho)

if __name__ == "__main__":
    from core import Gval, target
    # identity check
    for (b, p, q) in [(2, 5, 3), (2, 3, 5), (4, 5, 3), (2, 7, 5)]:
        M = T(2, p); N = T(b, q); muq = mus(b, q)
        for bits in itertools.product([1, -1], repeat=3 * (b + 1) - 1):
            Y = [list(bits[0:b + 1]), list(bits[b + 1:2 * b + 2]), list(bits[2 * b + 2:]) + [-1]]
            d = decomp(Y, p, q, M, muq)
            assert d['total'] * Fr(q) ** b == target(2, b, p, q) - Gval(Y, p, q, M, N), (Y,)
            assert all(x >= 0 for x in d['s']), (Y, d['s'])
        print(f"identity + s_j>=0 ok for (2,{b}) p={p} q={q}")
