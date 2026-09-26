"""End-to-end replay of the proof of Theorem B on every sign matrix of shape (2,b) (exact Fractions):
 (S)  s_j >= 0 for all j<b, and s_j > 0 when c_j is not +-s_2;
 (J)  J = max{j : c_j != (-1)^{j+1} s_2};  if J < b: state zeta_J == (-1)^J mu_{b-2-J} s_2  and  s_J > 2 delta_p rho;
      if J = b: c_b in {C,-E,B}; C: rho*Delta = need; -E: rho*Delta > need; B: sum_{j<b} s_j + kappa > 4 P rho;
 (EQ) Theta - G == 0 iff Y in {anti-checkerboard, truncated checkerboard};
 and the identity (Theta-G)/q^b = sum s_j + rho Delta(c_b) + kappa - need against the matrix model."""
import itertools, sys
from fractions import Fraction as Fr
from core import T, mus, dfun, delta_last, path, Gval, target
def hfun(Q, mu, A, B):
    return Q * abs(A - B) + mu * abs(B + Q * A) - (Q - mu) * abs(B) - Q * (1 + mu) * abs(A)
def run(b, p, q):
    p = Fr(p); q = Fr(q); Q = q - 1; P = p - 1
    M = T(2, p); N = T(b, q); mu = mus(b + 1, q)
    rho = mu[b - 1]; Dp = dfun(2, p); dp = delta_last(2, p); need = 2 * dp * rho
    chat = {j: Q * (1 + mu[j - 1]) / q for j in range(b)}
    s2 = [1, -1, 1]
    anti = [[-(-1) ** (i + j) for j in range(b + 1)] for i in range(3)]
    trunc = [[(-1) ** (i + j) for j in range(b + 1)] for i in range(3)]; trunc[2][b] = -1
    Fp = lambda c: sum(abs(sum(M[i][k] * c[k] for k in range(3))) for i in range(3))
    nY = 0; eqs = []
    minratio = {}
    for bits in itertools.product([1, -1], repeat=3 * (b + 1) - 1):
        Y = [list(bits[0:b + 1]), list(bits[b + 1:2 * b + 2]), list(bits[2 * b + 2:]) + [-1]]
        cols = [[Y[i][j] for i in range(3)] for j in range(b + 1)]
        r = [[sum(M[i][k] * cols[j][k] for k in range(3)) for j in range(b + 1)] for i in range(3)]
        z = [path(r[i], q) for i in range(3)]
        # column-path states zeta_j (convex combos of columns)
        zeta = {b - 1: [Fr(x) for x in cols[b]]}
        for j in range(b - 1, -1, -1):
            zeta[j - 1] = [(zeta[j][k] + Q * cols[j][k]) / q for k in range(3)]
        for j in range(b):   # consistency: z_j(r_i) = (T_2 zeta_j)_i
            assert all(z[i][j] == sum(M[i][k] * zeta[j][k] for k in range(3)) for i in range(3))
        s = [chat[j] * (Dp - Fp(cols[j])) - sum(hfun(Q, mu[j - 1], r[i][j], z[i][j]) for i in range(3)) / q for j in range(b)]
        kappa = 2 * max(Fr(0), -z[2][-1])
        Delta_b = Dp - Fp(cols[b])
        gap = target(2, b, p, q) - Gval(Y, p, q, M, N)
        assert gap == q ** b * (sum(s) + rho * Delta_b + kappa - need), "identity"
        for j in range(b):
            assert s[j] >= 0, "S"
            if cols[j] != s2 and cols[j] != [-x for x in s2]: assert s[j] > 0, "S strict"
        Jset = [j for j in range(b + 1) if cols[j] != [(-1) ** (j + 1) * x for x in s2]]
        if not Jset:
            assert Y == anti and gap == 0
            eqs.append('anti'); nY += 1; continue
        J = max(Jset)
        if J < b:
            eps = (-1) ** J; m = mu[b - 2 - J]
            assert zeta[J] == [eps * m * x for x in s2], "state"
            assert s[J] > need, ("FD1", Y, J)
            key = 'J<b'
            minratio[key] = min(minratio.get(key, 99), s[J] / need)
        else:
            cb = cols[b]
            if cb == [1, -1, -1]:
                assert rho * Delta_b == need
                if gap == 0:
                    assert Y == trunc; eqs.append('trunc')
            elif cb == [-1, -1, -1]:
                assert rho * Delta_b > need
            elif cb == [1, 1, -1]:
                assert rho * Delta_b == need - 4 * P * rho
                assert sum(s) + kappa > 4 * P * rho, ("FD2", Y)
                minratio['B'] = min(minratio.get('B', 99), (sum(s) + kappa) / (4 * P * rho))
            else:
                raise AssertionError("impossible last column")
        if gap == 0 and Y != trunc: raise AssertionError("unexpected equality")
        nY += 1
    assert sorted(eqs) == ['anti', 'trunc'], eqs
    print(f"(2,{b}) p={p} q={q}: {nY} sign matrices, all proof steps hold; equality exactly at anti & trunc; "
          f"min s_J/need (J<b) = {float(minratio['J<b']):.4f}, min FD2 ratio = {float(minratio['B']):.4f}")
    sys.stdout.flush()
if __name__ == "__main__":
    for (b, p, q) in [(2, 5, 3), (2, 3, 5), (2, 7, 3), (2, 3, 7), (2, 11, 13), (2, 13, 11), (2, Fr(11, 2), Fr(7, 2)), (2, 3, Fr(9, 2)),
                      (4, 5, 3), (4, 3, 5), (4, 7, 3), (4, 3, 7), (4, 5, 7), (4, 101, 3), (4, 3, 101)]:
        run(b, p, q)
