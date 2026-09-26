"""Column-path (q-path) slack decomposition (*) for general shapes, exact.
G/q^b = sum_k chat^q_k F(c_k) + (1/q) sum_{k<b} sum_u h_q(w^(u)_k, z_k(w^(u))) - 2 (z_{-1}(w^(a)))^-,
F(c) = ||T_a(p) c||_1, w^(u)_k = (T_a(p) c_k)_u.
Prints, for the near-tight configurations of a shape, the pieces:
  Edef = sum_k chat_k (D_a - F(c_k)), Hpos/Hneg = positive/negative parts of (1/q) sum h, corner = 2(z_{-1})^-,
  and total slack = Edef - H + corner  vs need = 2 delta_a rho_b.
"""
import itertools, sys
from fractions import Fraction as Fr
from core import T, Gval, dfun, delta_last, path, target


def mus(m, x):
    mu = {-1: Fr(1)}
    for k in range(m):
        mu[k] = (x - 1 - mu[k - 1]) / x
    return mu


def hfun(P, mu, A, B):
    return P * abs(A - B) + mu * abs(B + P * A) - (P - mu) * abs(B) - P * (1 + mu) * abs(A)


def decomp(Y, p, q):
    a = len(Y) - 1; b = len(Y[0]) - 1
    p = Fr(p); q = Fr(q); Pq = q - 1
    M = T(a, p)
    muq = mus(b, q)
    chat = {k: Pq * (1 + muq[k - 1]) / q for k in range(b)}; chat[b] = muq[b - 1]
    Da = dfun(a, p)
    cols = [[Fr(Y[i][k]) for i in range(a + 1)] for k in range(b + 1)]
    Mc = [[sum(M[u][i] * cols[k][i] for i in range(a + 1)) for u in range(a + 1)] for k in range(b + 1)]
    F = [sum(abs(v) for v in Mc[k]) for k in range(b + 1)]
    Edef = sum(chat[k] * (Da - F[k]) for k in range(b + 1))
    Hp = Fr(0); Hn = Fr(0); corner = Fr(0)
    for u in range(a + 1):
        w = [Mc[k][u] for k in range(b + 1)]
        z = path(w, q)
        for k in range(b):
            h = hfun(Pq, muq[k - 1], w[k], z[k]) / q
            if h > 0: Hp += h
            else: Hn += h
        if u == a:
            corner = 2 * max(Fr(0), -z[-1])
    G = Gval(Y, p, q) / q ** b
    tot = Edef - Hp - Hn + corner
    need = 2 * delta_last(a, p) * delta_last(b, q) / q ** b
    assert Da * sum(chat.values()) - tot == G, "identity"
    return dict(Edef=Edef, Hpos=Hp, Hneg=Hn, corner=corner, total=tot, need=need, G=G)


if __name__ == "__main__":
    for (a, b, p, q) in [(2, 2, 5, 3), (2, 2, 11, 3), (2, 2, 40, 3), (2, 4, 5, 3), (4, 2, 5, 3), (3, 3, 5, 3), (2, 2, 3, 5), (3, 3, 7, 3)]:
        tgt = target(a, b, p, q)
        M = T(a, p); N = T(b, q)
        res = []
        for bits in itertools.product([1, -1], repeat=(a + 1) * (b + 1) - 1):
            Y = [[0] * (b + 1) for _ in range(a + 1)]
            cells = [(i, j) for i in range(a + 1) for j in range(b + 1) if (i, j) != (a, b)]
            for (i, j), s in zip(cells, bits):
                Y[i][j] = s
            Y[a][b] = -1
            res.append((tgt - Gval(Y, p, q, M, N), Y))
        res.sort(key=lambda t: t[0])
        print(f"== (a,b,p,q)=({a},{b},{p},{q})")
        worst_ratio = None
        for gap, Y in res[:8]:
            d = decomp(Y, p, q)
            print(f"  gap={float(gap):10.4f} Y={'/'.join(''.join('+' if v>0 else '-' for v in r) for r in Y)} "
                  f"Edef={float(d['Edef']):.4f} Hpos={float(d['Hpos']):.4f} Hneg={float(d['Hneg']):.4f} corner={float(d['corner']):.4f} "
                  f"total={float(d['total']):.4f} need={float(d['need']):.4f}")
        # how often is H positive part not covered by the E-deficit of the same column? (global check)
        bad = 0
        for gap, Y in res:
            d = decomp(Y, p, q)
            if d['Hpos'] > d['Edef']:
                bad += 1
        print(f"  #Y with Hpos > Edef: {bad} of {len(res)}")
        sys.stdout.flush()
