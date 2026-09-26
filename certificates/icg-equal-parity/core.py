"""Core exact-arithmetic helpers for the equal-parity ICG problem (round 4).

Conventions (Jiang-Yang / q3-proof.md):
  T_k(x) (k+1)x(k+1):  t_ij = 0 (i+j<=k-2), -x^{k-1}(x-1) (i+j=k-1), x^{2k-i-j-2}(x-1)^2 (i+j>=k), i,j<k;
                        t_ik = t_ki = x^{k-i-1}(x-1) (i<k), t_kk = 1.
  n = p^a q^b, X 0/1 divisor matrix (X_ab = 0), Y = 2X - J, Z = T_a(p) Y T_b(q)^T,
  2E = ||n e_a e_b^T + Z||_1 = sum_{(u,v)!=(a,b)} |Z_uv| + n + Z_ab  (n + Z_ab >= 0 always).
  G(Y) := 2E - n = sum_{(u,v)!=(a,b)} |Z_uv| + Z_ab.
  Conjecture (a+b even):  max_{Y_ab=-1} G(Y) = d_a(p) d_b(q) - 2 delta_a(p) delta_b(q).
All functions accept int or Fraction x.
"""
from fractions import Fraction as Fr
import itertools


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
            else:
                t = i if i < k else j
                v = x ** (k - t - 1) * (x - 1)
            M[i][j] = v
    return M


def mus(m, x):
    """potential mu_{-1}=1, mu_k=(x-1-mu_{k-1})/x, k=0..m-1 (dict)."""
    x = Fr(x)
    mu = {-1: Fr(1)}
    for k in range(m):
        mu[k] = (x - 1 - mu[k - 1]) / x
    return mu


def delta_last(m, x):
    """delta_m(x) = x^m mu_{m-1} = (x^m (x-1) + 2(-1)^m)/(x+1)."""
    x = Fr(x)
    return (x ** m * (x - 1) + 2 * (-1) ** m) / (x + 1)


def dfun(m, x):
    """d_m(x) = ||T_m(x) s_m||_1 (closed form)."""
    x = Fr(x)
    if m == 0:
        return Fr(1)
    return (2 * m + 1) * x ** m + 4 * sum((-1) ** (m - j) * (j + 1) * x ** j for j in range(m))


def path(w, x):
    """z[k], k=-1..m-1: z[m-1]=w[m], z[k-1]=(z[k]+(x-1)w[k])/x."""
    x = Fr(x)
    m = len(w) - 1
    z = {m - 1: Fr(w[m])}
    for k in range(m - 1, -1, -1):
        z[k - 1] = (z[k] + (x - 1) * w[k]) / x
    return z


def incr(w, x):
    """L_m(x) w = (z_{-1}, z_{-1}-z_0, ..., z_{m-2}-z_{m-1}) indexed -1..m-1 as a list [idx+1]."""
    z = path(w, x)
    m = len(w) - 1
    return [z[-1]] + [z[k - 1] - z[k] for k in range(m)]


def matmul(A, B):
    return [[sum(A[i][t] * B[t][j] for t in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def transpose(A):
    return [list(r) for r in zip(*A)]


def Zmat(Y, p, q, M=None, N=None):
    a = len(Y) - 1
    b = len(Y[0]) - 1
    M = M or T(a, p)
    N = N or T(b, q)
    return matmul(matmul(M, Y), transpose(N))


def Gval(Y, p, q, M=None, N=None):
    a = len(Y) - 1
    b = len(Y[0]) - 1
    Z = Zmat(Y, p, q, M, N)
    s = sum(abs(Z[u][v]) for u in range(a + 1) for v in range(b + 1))
    return s - abs(Z[a][b]) + Z[a][b]


def target(a, b, p, q):
    return dfun(a, p) * dfun(b, q) - 2 * delta_last(a, p) * delta_last(b, q)


def checker(a, b, sign=1):
    return [[sign * (-1) ** (i + j) for j in range(b + 1)] for i in range(a + 1)]


def truncated(a, b):
    Y = checker(a, b, 1)
    Y[a][b] = -1
    return Y


def all_sign_matrices(a, b, fix_corner=True):
    cells = [(i, j) for i in range(a + 1) for j in range(b + 1)]
    for bits in itertools.product([1, -1], repeat=len(cells)):
        Y = [[0] * (b + 1) for _ in range(a + 1)]
        for (i, j), s in zip(cells, bits):
            Y[i][j] = s
        if fix_corner and Y[a][b] != -1:
            continue
        yield Y


if __name__ == "__main__":
    # sanity: G of the two conjectured maximisers equals the target (exact)
    for (a, b) in [(1, 1), (2, 2), (1, 3), (3, 1), (2, 4), (3, 3)]:
        for (p, q) in [(5, 3), (3, 5), (7, 5), (Fr(11, 2), Fr(7, 2)), (5, 7)]:
            t = target(a, b, p, q)
            assert Gval(checker(a, b, -1), p, q) == t, (a, b, p, q)
            assert Gval(truncated(a, b), p, q) == t, (a, b, p, q, Gval(truncated(a, b), p, q), t)
            for m, x in ((a, p), (b, q)):
                Tm = T(m, x)
                s = [(-1) ** i for i in range(m + 1)]
                assert sum(abs(sum(Tm[i][j] * s[j] for j in range(m + 1))) for i in range(m + 1)) == dfun(m, x)
                assert delta_last(m, x) == Fr(x) ** m * mus(m, x)[m - 1]
    print("core sanity ok")
