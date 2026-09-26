"""Exact integer model for the energy of ICG(p^a q^b, D).

E(D) = || T_a(p) X T_b(q)^T ||_1 (Jiang-Yang Prop. 2.2), where X is the
(a+1)x(b+1) 0/1 divisor matrix (x_ij = 1 iff p^i q^j in D) and
T_k(x)_{ij} = phi(x^{k-i}) c_{x^{k-j}}(x^i).
All arithmetic is exact Python integers.
"""
from itertools import product


def phi_pp(x, e):
    """phi(x^e) for prime x (formula valid as a polynomial for any integer x)."""
    return 1 if e == 0 else x ** (e - 1) * (x - 1)


def ram_pp(x, k, i):
    """Ramanujan sum c_{x^k}(x^i) for prime x (i may be 'inf' -> use large)."""
    if k == 0:
        return 1
    if k <= i:
        return x ** (k - 1) * (x - 1)
    if k == i + 1:
        return -x ** (k - 1)
    return 0


def T(k, x):
    return [[phi_pp(x, k - i) * ram_pp(x, k - j, i) for j in range(k + 1)] for i in range(k + 1)]


def delta(k, x):
    """Jiang-Yang diagonal Delta_k(x) entries (3.3)-(3.4); exact integers."""
    def R(i):
        return sum((-1) ** (i - t) * x ** t for t in range(i + 1))
    d = [2 * x ** (k - i - 1) * (x - 1) * R(i) for i in range(k)]
    d.append(2 * R(k) - x ** k)
    return d


def dpoly(k, x):
    return (2 * k + 1) * x ** k + 4 * sum((-1) ** (k - j) * (j + 1) * x ** j for j in range(k))


def matmul(A, B):
    return [[sum(A[i][t] * B[t][j] for t in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def transpose(A):
    return [list(r) for r in zip(*A)]


def energy(X, p, q, a, b, M=None, N=None):
    M = M or T(a, p)
    N = N or T(b, q)
    Z = matmul(matmul(M, X), transpose(N))
    return sum(abs(v) for row in Z for v in row)


def checkerboard(a, b):
    return [[1 if (i + j) % 2 == 0 else 0 for j in range(b + 1)] for i in range(a + 1)]


def mask_to_X(mask, a, b):
    """Bits in row-major order over (i,j) != (a,b)."""
    cells = [(i, j) for i in range(a + 1) for j in range(b + 1) if (i, j) != (a, b)]
    X = [[0] * (b + 1) for _ in range(a + 1)]
    for t, (i, j) in enumerate(cells):
        if mask >> t & 1:
            X[i][j] = 1
    return X


def X_to_mask(X, a, b):
    cells = [(i, j) for i in range(a + 1) for j in range(b + 1) if (i, j) != (a, b)]
    assert X[a][b] == 0
    return sum(1 << t for t, (i, j) in enumerate(cells) if X[i][j])


if __name__ == "__main__":
    # sanity: Roldan closed form at r=s=1
    for p, q in [(5, 3), (7, 3), (3, 5), (11, 13)]:
        E = energy(checkerboard(2, 3), p, q, 2, 3)
        n = p * p * q ** 3
        assert 2 * E == n + dpoly(2, p) * dpoly(3, q), (p, q)
        roldan = ((5 * p * p - 8 * p + 4) * (q - 1) * (3 * q * q - 2 * q + 1)
                  + (p - 1) * (2 * p - 1) * (q ** 3 - 2 * q * q + 2 * q - 2)
                  + (p * p - 2 * p + 2) * (q - 1) * (q * q + 1) + (p - 1) * q ** 3)
        assert E == roldan
    for k in range(1, 8):
        for x in (3, 5, 7):
            assert sum(delta(k, x)) == dpoly(k, x)
    print("model sanity ok")
