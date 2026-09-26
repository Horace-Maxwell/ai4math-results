"""Exact replay of the proof of Theorem (sign-matrix form, a = 2) as written in the new Section 10,
in the paper's notation: x = q, P = x - 1, R = p - 1, M = T_2(p), N = T_b(q).
Everything is built from the definitions in note.tex (T_k, path (1), potential, h of Lemma 9)."""
from fractions import Fraction as F
import itertools, random, sys

def T(k, x):
    t = [[F(0)] * (k + 1) for _ in range(k + 1)]
    for i in range(k):
        for j in range(k):
            if i + j <= k - 2:
                t[i][j] = F(0)
            elif i + j == k - 1:
                t[i][j] = -x ** (k - 1) * (x - 1)
            else:
                t[i][j] = x ** (2 * k - i - j - 2) * (x - 1) ** 2
    for i in range(k):
        t[i][k] = t[k][i] = x ** (k - i - 1) * (x - 1)
    t[k][k] = F(1)
    return t

def matvec(A, v):
    return [sum(a * b for a, b in zip(row, v)) for row in A]

def sgnvec(k):
    return [F((-1) ** i) for i in range(k + 1)]

def d_delta(k, x):
    v = matvec(T(k, x), sgnvec(k))
    return sum(abs(a) for a in v), v[k]

def h(P, mu, A, B):
    return P * abs(A - B) + mu * abs(B + P * A) - (P - mu) * abs(B) - P * (1 + mu) * abs(A)

def G_of(Y, p, q, b):
    M, N = T(2, p), T(b, q)
    MY = [[sum(M[i][l] * Y[l][j] for l in range(3)) for j in range(b + 1)] for i in range(3)]
    Z = [[sum(MY[i][l] * N[j][l] for l in range(b + 1)) for j in range(b + 1)] for i in range(3)]
    tot = sum(abs(Z[i][j]) for i in range(3) for j in range(b + 1) if (i, j) != (2, b)) + Z[2][b]
    return tot

def check(p, q, b, Y, stats):
    x = q; P = x - 1; R = p - 1
    M = T(2, p)
    d2, del2 = d_delta(2, p); db, delb = d_delta(b, q)
    assert d2 == 5 * R**2 + 2 * R + 1 and del2 == R**2 + 1
    Theta = d2 * db - 2 * del2 * delb
    mu = {-1: F(1)}
    for j in range(0, b + 1):
        mu[j] = (P - mu[j - 1]) / x
    rho = mu[b - 1]
    assert rho == delb / x**b
    cols = [[Y[i][j] for i in range(3)] for j in range(b + 1)]
    Mc = [matvec(M, c) for c in cols]
    Delta = [d2 - sum(abs(a) for a in v) for v in Mc]
    zeta = {b - 1: cols[b][:]}
    for j in range(b - 1, -1, -1):
        zeta[j - 1] = [(zeta[j][i] + P * cols[j][i]) / x for i in range(3)]
    Mz = {j: matvec(M, zeta[j]) for j in zeta}
    psi = []
    for j in range(b):
        m_ = mu[j - 1]
        cells = [h(P, m_, Mc[j][i], Mz[j][i]) for i in range(3)]
        psi.append(P * (1 + m_) * Delta[j] - sum(cells))
    G = G_of(Y, p, q, b)
    kap = 2 * x * max(F(0), -Mz[-1][2])
    lhs = (Theta - G) / x ** (b - 1)
    rhs = sum(psi) + x * rho * (Delta[b] - 2 * del2) + kap
    assert lhs == rhs, 'column identity'
    # Lemma S
    s2 = [1, -1, 1]
    for j in range(b):
        assert psi[j] >= 0
        if cols[j] != s2 and cols[j] != [-v for v in s2]:
            assert psi[j] > 0
    # case analysis
    anti = [[F(-((-1) ** j)) * v for v in s2] for j in range(b + 1)]  # (-1)^{j+1} s2
    Ym = all(cols[j] == anti[j] for j in range(b + 1))
    if Ym:
        assert G == Theta; stats['Ym'] += 1; return G, Theta
    J = max(j for j in range(b + 1) if cols[j] != anti[j])
    if J < b:
        eps = (-1) ** J; m = mu[b - 2 - J]
        assert zeta[J] == [eps * m * v for v in s2], 'exact state'
        assert psi[J] > 2 * x * del2 * rho, 'FD1'
        stats['FD1'] += 1
        assert G < Theta
    else:
        cb = cols[b]
        if cb == [-1, -1, -1]:
            assert Delta[b] == 4 * R**2; assert G < Theta; stats['-g4'] += 1
        elif cb == [1, -1, -1]:
            assert Delta[b] == 2 * del2
            assert (Theta - G) / x ** (b - 1) == sum(psi) + kap
            Yp = all(cols[j] == [((-1) ** j) * v for v in s2] for j in range(b))
            if Yp:
                assert G == Theta and all(ps == 0 for ps in psi) and kap == 0
                stats['Yp'] += 1
            else:
                assert G < Theta; stats['g3'] += 1
        elif cb == [1, 1, -1]:
            assert Delta[b] == 2 * (R - 1)**2
            need = 4 * R * x * rho
            assert x * rho == P - mu[b - 2]
            if cols[b - 1] != [-1, -1, 1] or R >= 4:
                assert psi[b - 1] > need, 'FD2(a)'
                stats['FD2a'] += 1
            else:
                assert R == 2
                assert psi[b - 1] == 2 * P * (1 + mu[b - 2])
                assert zeta[b - 2] == [-mu[0] * v for v in [1, 1, -1]]
                assert psi[b - 2] >= 2 * P * (1 + mu[b - 3]), 'dominance'
                assert psi[b - 1] + psi[b - 2] > need, 'two columns'
                stats['FD2b'] += 1
            assert G < Theta
        else:
            raise AssertionError('unexpected last column')
    return G, Theta

def run(pairs, bs, exhaustive_upto=4, nrand=3000, seed=1):
    rnd = random.Random(seed)
    for (p, q) in pairs:
        for b in bs:
            stats = dict(Ym=0, Yp=0, FD1=0, FD2a=0, FD2b=0, g3=0, **{'-g4': 0})
            if b <= exhaustive_upto:
                it = itertools.product([1, -1], repeat=3 * (b + 1) - 1)
            else:
                it = (tuple(rnd.choice([1, -1]) for _ in range(3 * (b + 1) - 1)) for _ in range(nrand))
            n = 0
            for bits in it:
                flat = list(bits) + [-1]
                Y = [[F(flat[i * (b + 1) + j]) for j in range(b + 1)] for i in range(3)]
                check(p, q, b, Y, stats); n += 1
            # always include the two extremal matrices and near-extremal ones for random runs
            print(f'p={p} q={q} b={b}: {n} matrices OK', stats, flush=True)

if __name__ == '__main__':
    pairs = [(F(5), F(3)), (F(3), F(5)), (F(7), F(3)), (F(3), F(7)), (F(11, 2), F(7, 2)),
             (F(3), F(11, 2)), (F(101), F(3)), (F(3), F(101)), (F(5), F(5)), (F(13), F(11))]
    run(pairs, [2, 4])
    run([(F(5), F(3)), (F(3), F(5)), (F(3), F(41, 4)), (F(51, 10), F(31, 10))], [6, 8], nrand=1500)
    print('ALL OK')
