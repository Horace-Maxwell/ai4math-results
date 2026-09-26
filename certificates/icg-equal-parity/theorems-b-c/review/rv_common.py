"""Referee's own exact helpers (independent of the authors' core.py / formulas.py).

Everything is built from the definitions in note.tex:
  T_k(x): t_ij = 0 (i+j<=k-2), -x^{k-1}(x-1) (i+j=k-1), x^{2k-i-j-2}(x-1)^2 (i+j>=k)  for i,j<k;
          t_ik = t_ki = x^{k-i-1}(x-1) (i<k), t_kk = 1.
  path:   z_{k-1} = w_k,  z_{j-1} = (z_j + (x-1) w_j)/x.
  potential: mu_{-1}=1, mu_j = (x-1-mu_{j-1})/x.
  cell:   h_mu(A,B) = Q|A-B| + mu|B+QA| - (Q-mu)|B| - Q(1+mu)|A|   (Q = q-1)
  G(Y) = sum_{(i,j)!=(a,b)} |Z_ij| + Z_ab,  Z = T_a(p) Y T_b(q)^T.
All arithmetic is exact (Fraction).  No code is imported from the authors' folder.
"""
from fractions import Fraction as Fr
from math import gcd


def T(k, x):
    x = Fr(x)
    M = [[Fr(0)] * (k + 1) for _ in range(k + 1)]
    for i in range(k + 1):
        for j in range(k + 1):
            if i < k and j < k:
                if i + j <= k - 2:
                    v = Fr(0)
                elif i + j == k - 1:
                    v = -x ** (k - 1) * (x - 1)
                else:
                    v = x ** (2 * k - i - j - 2) * (x - 1) ** 2
            elif i == k and j == k:
                v = Fr(1)
            elif i < k:  # j == k
                v = x ** (k - i - 1) * (x - 1)
            else:        # i == k, j < k
                v = x ** (k - j - 1) * (x - 1)
            M[i][j] = v
    return M


# ---------- Ramanujan-sum model (prime x only), used as an independent cross-check of T ----------
def mobius(n):
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


def ramanujan(m, t):
    """c_m(t) = sum_{d | gcd(m,t)} mu(m/d) d  (t may be 0: gcd(m,0)=m)."""
    g = gcd(m, t) if t != 0 else m
    return sum(mobius(m // d) * d for d in range(1, g + 1) if g % d == 0)


def phi(n):
    return sum(1 for k in range(1, n + 1) if gcd(k, n) == 1)


def T_ramanujan(k, x):
    """t_ij = phi(x^{k-i}) c_{x^{k-j}}(x^i) for prime x."""
    return [[Fr(phi(x ** (k - i)) * ramanujan(x ** (k - j), x ** i)) for j in range(k + 1)] for i in range(k + 1)]


# ---------- linear algebra ----------
def matvec(M, v):
    return [sum(M[i][t] * v[t] for t in range(len(v))) for i in range(len(M))]


def matmul(A, B):
    return [[sum(A[i][t] * B[t][j] for t in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def transpose(A):
    return [list(r) for r in zip(*A)]


def l1(v):
    return sum(abs(x) for x in v)


# ---------- path, potential, closed forms ----------
def path(w, x):
    """returns dict z[j], j=-1..k-1."""
    x = Fr(x)
    k = len(w) - 1
    z = {k - 1: Fr(w[k])}
    for j in range(k - 1, -1, -1):
        z[j - 1] = (z[j] + (x - 1) * w[j]) / x
    return z


def pot(n, x):
    """mu[-1..n-1]."""
    x = Fr(x)
    mu = {-1: Fr(1)}
    for j in range(n):
        mu[j] = (x - 1 - mu[j - 1]) / x
    return mu


def s_vec(k):
    return [(-1) ** i for i in range(k + 1)]


def d_def(k, x):
    """d_k(x) := ||T_k(x) s_k||_1 (definition), d_0 = 1."""
    if k == 0:
        return Fr(1)
    return l1(matvec(T(k, x), s_vec(k)))


def delta_def(k, x):
    """delta_k(x) := (T_k(x) s_k)_k."""
    if k == 0:
        return Fr(1)
    return matvec(T(k, x), s_vec(k))[k]


def d_closed(k, x):
    x = Fr(x)
    return (2 * k + 1) * x ** k + 4 * sum((-1) ** (k - j) * (j + 1) * x ** j for j in range(k))


def delta_closed(k, x):
    x = Fr(x)
    return (x ** k * (x - 1) + 2 * (-1) ** k) / (x + 1)


def hcell(Q, mu, A, B):
    return Q * abs(A - B) + mu * abs(B + Q * A) - (Q - mu) * abs(B) - Q * (1 + mu) * abs(A)


# ---------- the functional G and the target ----------
def Zmat(Y, p, q, M=None, N=None):
    a = len(Y) - 1
    b = len(Y[0]) - 1
    M = M if M is not None else T(a, p)
    N = N if N is not None else T(b, q)
    return matmul(matmul(M, Y), transpose(N))


def G(Y, p, q, M=None, N=None):
    Z = Zmat(Y, p, q, M, N)
    a = len(Y) - 1
    b = len(Y[0]) - 1
    tot = sum(abs(Z[i][j]) for i in range(a + 1) for j in range(b + 1) if (i, j) != (a, b))
    return tot + Z[a][b]


def Theta(a, b, p, q):
    return d_def(a, p) * d_def(b, q) - 2 * delta_def(a, p) * delta_def(b, q)


def Yminus(a, b):
    return [[-(-1) ** (i + j) for j in range(b + 1)] for i in range(a + 1)]


def Yplus(a, b):
    Y = [[(-1) ** (i + j) for j in range(b + 1)] for i in range(a + 1)]
    Y[a][b] = -1
    return Y


# column vectors for a = 2
S2 = (1, -1, 1)
TYPES = {'A': (1, -1, 1), 'B': (1, 1, -1), 'C': (1, -1, -1), 'E': (1, 1, 1)}


def neg(v):
    return tuple(-x for x in v)


def scal(c, v):
    return tuple(c * x for x in v)
