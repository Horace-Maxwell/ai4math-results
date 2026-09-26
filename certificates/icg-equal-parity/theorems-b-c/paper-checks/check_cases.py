"""Random exact checks of the one-column statements of Section 10 on the whole parameter boxes used
in the text (not only at the true potential values).  Paper notation: R = p-1, P = q-1 = x-1."""
from fractions import Fraction as F
import random

def h(P, mu, A, B):
    return P * abs(A - B) + mu * abs(B + P * A) - (P - mu) * abs(B) - P * (1 + mu) * abs(A)

def Mmat(R):
    p = R + 1
    return [[0, -p * R, p * R], [-p * R, R * R, R], [p * R, R, 1]]

def mv(M, v):
    return [sum(a * b for a, b in zip(r, v)) for r in M]

def psi(R, P, mu, c, zeta):
    M = Mmat(R)
    A, B = mv(M, c), mv(M, zeta)
    d2 = 5 * R * R + 2 * R + 1
    Delta = d2 - sum(abs(a) for a in A)
    return P * (1 + mu) * Delta - sum(h(P, mu, A[i], B[i]) for i in range(3))

rnd = random.Random(7)
def rfrac(lo, hi):
    return lo + (hi - lo) * F(rnd.randint(0, 10**6), 10**6)

s2 = [1, -1, 1]; g2 = [1, 1, -1]; g3 = [1, -1, -1]; g4 = [1, 1, 1]
allc = [[a, b, c] for a in (1, -1) for b in (1, -1) for c in (1, -1)]
N = 40000
cnt = 0
for it in range(N):
    if it % 2 == 0:
        R, P = rfrac(4, 4 + rnd.choice([1, 10, 100])), rfrac(2, 2 + rnd.choice([1, 10, 100]))
    else:
        R, P = F(2), rfrac(4, 4 + rnd.choice([1, 10, 100]))
    if it % 7 == 0:  # boundary corners
        R, P = (F(4), F(2)) if it % 14 == 0 else (F(2), F(4))
    x = P + 1; p = R + 1
    mu0 = (P - 1) / x; mu1 = (P * P + 1) / (x * x)
    T = (R * R + 1) * (P * P + 1)
    mu = rfrac(mu0, 1); m = rfrac(mu0, 1)
    if it % 5 == 0: mu = F(1)
    if it % 5 == 1: m = F(1)
    if it % 5 == 2: mu = mu0
    if it % 5 == 3: m = mu0
    d2 = 5 * R * R + 2 * R + 1
    st = [m * v for v in s2]
    # Lemma S explicit bounds, arbitrary state in the cube
    zeta = [rfrac(-1, 1) for _ in range(3)]
    Bz = mv(Mmat(R), zeta)
    mu_any = rfrac(0, 1)
    for c in allc:
        val = psi(R, P, mu_any, c, zeta)
        assert val >= 0
        if c not in (s2, [-v for v in s2]):
            assert val > 0
        if c in (g3, [-v for v in g3]):
            assert val >= 2 * P * (1 + mu_any) * (R * R + 1) - 2 * mu_any * abs(Bz[0])
        if c in (g4, [-v for v in g4]):
            assert val >= 4 * P * R * R * (1 + mu_any) - 2 * mu_any * (abs(Bz[0]) + abs(Bz[1]))
    # FD1 (state m s2)
    K = x * (P - mu) * m
    assert K >= (P - 1) ** 2
    v = psi(R, P, mu, s2, st); assert v == 2 * (P - mu) * m * d2; assert x * v > 2 * T
    v = psi(R, P, mu, g2, st)
    if m * R <= 1:
        assert v == 2 * P * (1 + mu) * (R - 1) ** 2 + 2 * (P - mu) * m * (3 * R * R + 1)
    else:
        assert v == 2 * P * (1 + mu) * (R - 1) ** 2 + 2 * (P - mu) * m * (R * R + 1) - 4 * R * (mu * m * R - P)
        a0 = 2 * (R * R + 1) * (P - 1); a1 = 2 * P * x * (R - 1) ** 2
        a2 = 2 * P * x * (R * R + 1); a3 = -2 * x * (3 * R * R + 1)
        assert x * v - 2 * T == a0 + a1 * mu + a2 * m + a3 * mu * m
    assert x * v > 2 * T
    v = psi(R, P, mu, [-a for a in g2], st)
    if m * R <= P:
        assert v == 2 * P * (1 + mu) * (R - 1) ** 2 + 4 * (P - mu) * m * p * R
    else:
        assert R >= 4
        assert v == 2 * P * (1 + mu) * (R - 1) ** 2 + 4 * (P - mu) * m * p * R - 4 * mu * R * (m * R - P)
        assert v == 2 * P * (1 + mu) * (R - 1) ** 2 + 4 * mu * P * R + 4 * m * R * (P * p - mu * (2 * R + 1))
        assert v >= 2 * P * (R - 1) ** 2 + 4 * P * P * (R + 1) + 2 * mu * P * (R * R - 4 * R - 1)
    assert x * v > 2 * T
    for c in (g3, [-a for a in g3]):
        v = psi(R, P, mu, c, st)
        assert v >= 2 * P * (1 + mu) * (R * R + 1) - 4 * mu * m * p * R
        if m <= mu1:
            assert x * v > 2 * T
        if m == 1:
            assert v > 2 * (R * R + 1) * (P - mu)
    for c in (g4, [-a for a in g4]):
        v = psi(R, P, mu, c, st)
        assert v >= 4 * P * R * R * (1 + mu) - 4 * mu * m * R * (2 * R + 1) >= 4 * R * (P * R - 1)
        assert x * v > 2 * T
    # FD2(a): state g2, any mu in [0,1]
    mu2 = rfrac(0, 1)
    for c in allc:
        if c == [-a for a in g2] and R < 4:
            v = psi(R, P, mu2, c, g2); assert v == 2 * P * (1 + mu2) * (R - 1) ** 2
            continue
        assert psi(R, P, mu2, c, g2) > 4 * R * (P - mu2)
    # FD2(b): R = 2, state -mu0 g2, mu in [mu0, 1]
    if R == 2:
        stb = [-mu0 * a for a in g2]
        assert 22 * (P - mu) * mu0 >= 2 * P * (1 + mu)
        for c in allc:
            assert psi(R, P, mu, c, stb) >= 2 * P * (1 + mu)
        # two columns: u = mu_{b-2}, v = mu_{b-3} > P/(P+2), x u = P - v, x rho = P - u
        vv = rfrac(P / (P + 2), mu1) if rnd.random() < 0.9 else F(1)
        if vv <= P / (P + 2): vv = F(1)
        u = (P - vv) / x; xrho = P - u
        lhs = 2 * P * (1 + u) + 2 * P * (1 + vv) - 8 * xrho
        assert x * lhs == 2 * (P - 2) * ((P + 2) * vv - P) and lhs > 0
    cnt += 1
print('random box checks OK:', cnt)
