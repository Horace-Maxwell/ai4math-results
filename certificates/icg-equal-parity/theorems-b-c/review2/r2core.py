"""Referee-2 core (independent of the authors' core.py / generic_prover.py).

Exact arithmetic only (int / Fraction).
  T(k, x)        : weighted Ramanujan transform T_k(x), from the closed formula of Paper 1 (sec. 2), real x > 1.
  T_ram(k, x)    : the same matrix for a PRIME x from the Ramanujan-sum definition t_ij = phi(x^{k-i}) c_{x^{k-j}}(x^i),
                   with c_m(n) = sum_{d | gcd(m,n)} Moebius(m/d) d  (used only to cross-check T).
  mus(n, q)      : potential mu_{-1} = 1, mu_j = (q-1-mu_{j-1})/q, returned as dict j -> mu_j for j = -1..n-1.
  G(Y, M, N)     : sum_{(i,j) != (a,b)} |Z_ij| + Z_ab, Z = M Y N^T  (matrix model, eq. (G) of Paper 1).
  dd(k,x), de(k,x): d_k(x) = ||T_k s_k||_1 and delta_k(x) = (T_k s_k)_k computed from the matrix (not from closed forms).
  h(Q, mu, A, B) : the cell function of Paper 1 Lemma 6 with P <- Q.
"""
from fractions import Fraction as Fr
import itertools


def T(k, x):
    x = Fr(x)
    n = k + 1
    M = [[Fr(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i == k and j == k:
                M[i][j] = Fr(1)
            elif i == k or j == k:
                e = k - min(i, j)          # the other index
                M[i][j] = x ** (e - 1) * (x - 1)
            else:
                if i + j <= k - 2:
                    M[i][j] = Fr(0)
                elif i + j == k - 1:
                    M[i][j] = -(x ** (k - 1)) * (x - 1)
                else:
                    M[i][j] = x ** (2 * k - i - j - 2) * (x - 1) ** 2
    return M


def _moebius(n):
    res, d, m = 1, 2, n
    while d * d <= m:
        if m % d == 0:
            m //= d
            if m % d == 0:
                return 0
            res = -res
        d += 1
    if m > 1:
        res = -res
    return res


def ramanujan(m, n):
    from math import gcd
    g = gcd(m, n)
    return sum(_moebius(m // d) * d for d in range(1, g + 1) if g % d == 0)


def phi_pp(x, e):
    return 1 if e == 0 else x ** (e - 1) * (x - 1)


def T_ram(k, x):
    return [[phi_pp(x, k - i) * ramanujan(x ** (k - j), x ** i) for j in range(k + 1)] for i in range(k + 1)]


def mus(n, q):
    q = Fr(q)
    mu = {-1: Fr(1)}
    for j in range(n):
        mu[j] = (q - 1 - mu[j - 1]) / q
    return mu


def matvec(M, v):
    return [sum(M[i][k] * v[k] for k in range(len(v))) for i in range(len(M))]


def l1(v):
    return sum(abs(x) for x in v)


def svec(k):
    return [(-1) ** i for i in range(k + 1)]


def dd(k, x):
    return l1(matvec(T(k, x), svec(k)))


def de(k, x):
    return matvec(T(k, x), svec(k))[k]


def d_closed(k, x):
    x = Fr(x)
    return (2 * k + 1) * x ** k + 4 * sum((-1) ** (k - j) * (j + 1) * x ** j for j in range(k))


def delta_closed(k, x):
    x = Fr(x)
    return (x ** k * (x - 1) + 2 * (-1) ** k) / (x + 1)


def Zmat(Y, M, N):
    a, b = len(Y) - 1, len(Y[0]) - 1
    MY = [[sum(M[i][k] * Y[k][j] for k in range(a + 1)) for j in range(b + 1)] for i in range(a + 1)]
    return [[sum(MY[i][j] * N[v][j] for j in range(b + 1)) for v in range(b + 1)] for i in range(a + 1)]


def G(Y, M, N):
    Z = Zmat(Y, M, N)
    a, b = len(Y) - 1, len(Y[0]) - 1
    return sum(abs(Z[i][v]) for i in range(a + 1) for v in range(b + 1)) - abs(Z[a][b]) + Z[a][b]


def Theta(a, b, p, q):
    return dd(a, p) * dd(b, q) - 2 * de(a, p) * de(b, q)


def anti(a, b):
    return [[-(-1) ** (i + j) for j in range(b + 1)] for i in range(a + 1)]


def trunc(a, b):
    Y = [[(-1) ** (i + j) for j in range(b + 1)] for i in range(a + 1)]
    Y[a][b] = -1
    return Y


def h(Q, mu, A, B):
    return Q * abs(A - B) + mu * abs(B + Q * A) - (Q - mu) * abs(B) - Q * (1 + mu) * abs(A)


def colpath(cols, q):
    """column-path states zeta_j (j = b-1 .. -1) for columns c_0..c_b (lists)."""
    q = Fr(q)
    Q = q - 1
    b = len(cols) - 1
    z = {b - 1: [Fr(x) for x in cols[b]]}
    for j in range(b - 1, -1, -1):
        z[j - 1] = [(z[j][k] + Q * cols[j][k]) / q for k in range(len(cols[j]))]
    return z


def surplus_direct(M, Da, Q, q, mu, c, zeta):
    """s(c, zeta) = Q(1+mu)/q * Delta(c) - (1/q) sum_i h_mu((Mc)_i, (M zeta)_i), computed from the definition."""
    A = matvec(M, c)
    B = matvec(M, zeta)
    return Q * (1 + mu) / q * (Da - l1(A)) - sum(h(Q, mu, A[i], B[i]) for i in range(len(A))) / q
