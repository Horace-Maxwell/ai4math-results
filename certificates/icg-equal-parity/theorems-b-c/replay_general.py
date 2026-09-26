"""Generic replay (any a, b with a+b even) on every sign matrix: Proposition 1 identity, Lemma S (s_j >= 0, strict off +-s_a),
first deviation J: if J < b then the state is (-1)^J mu_{b-2-J} s_a and s_J > 2 delta_a rho; if J = b then either
rho*Delta(c_b) >= 2 delta_a rho (equality only for the truncated column) or the remaining terms pay (Theta > G);
and the equality set is exactly {Y-, Y+}."""
import itertools, sys
from fractions import Fraction as Fr
from core import T, mus, dfun, delta_last, path, Gval, target
def hfun(Q, mu, A, B):
    return Q * abs(A - B) + mu * abs(B + Q * A) - (Q - mu) * abs(B) - Q * (1 + mu) * abs(A)
def run(a, b, p, q):
    p = Fr(p); q = Fr(q); Q = q - 1
    M = T(a, p); N = T(b, q); mu = mus(b + 1, q)
    rho = mu[b - 1]; Da = dfun(a, p); da = delta_last(a, p); need = 2 * da * rho
    sa = [(-1) ** i for i in range(a + 1)]
    anti = [[-(-1) ** (i + j) for j in range(b + 1)] for i in range(a + 1)]
    trunc = [[(-1) ** (i + j) for j in range(b + 1)] for i in range(a + 1)]; trunc[a][b] = -1
    Fp = lambda c: sum(abs(sum(M[i][k] * c[k] for k in range(a + 1))) for i in range(a + 1))
    eqs = []; n = 0; minr = None
    for bits in itertools.product([1, -1], repeat=(a + 1) * (b + 1) - 1):
        flat = list(bits) + [-1]
        Y = [flat[i * (b + 1):(i + 1) * (b + 1)] for i in range(a + 1)]
        cols = [[Y[i][j] for i in range(a + 1)] for j in range(b + 1)]
        r = [[sum(M[i][k] * cols[j][k] for k in range(a + 1)) for j in range(b + 1)] for i in range(a + 1)]
        z = [path(r[i], q) for i in range(a + 1)]
        zeta = {b - 1: [Fr(x) for x in cols[b]]}
        for j in range(b - 1, -1, -1):
            zeta[j - 1] = [(zeta[j][k] + Q * cols[j][k]) / q for k in range(a + 1)]
        s = [Q * (1 + mu[j - 1]) / q * (Da - Fp(cols[j])) - sum(hfun(Q, mu[j - 1], r[i][j], z[i][j]) for i in range(a + 1)) / q for j in range(b)]
        kappa = 2 * max(Fr(0), -z[a][-1]); Db = Da - Fp(cols[b])
        gap = target(a, b, p, q) - Gval(Y, p, q, M, N)
        assert gap == q ** b * (sum(s) + rho * Db + kappa - need)
        for j in range(b):
            assert s[j] >= 0
            if cols[j] != sa and cols[j] != [-x for x in sa]: assert s[j] > 0
        Js = [j for j in range(b + 1) if cols[j] != [-(-1) ** j * x for x in sa]]
        if not Js:
            assert Y == anti and gap == 0; eqs.append('anti'); n += 1; continue
        J = max(Js)
        if J < b:
            assert zeta[J] == [(-1) ** J * mu[b - 2 - J] * x for x in sa]
            assert s[J] > need
            rr = s[J] / need; minr = rr if minr is None or rr < minr else minr
        else:
            if Db > 2 * da: pass
            elif Db == 2 * da:
                assert cols[b] == [trunc[i][b] for i in range(a + 1)], "another column with Delta = 2 delta"
            else:
                assert sum(s) + kappa > (2 * da - Db) * rho
        assert gap >= 0
        if gap == 0:
            assert Y == trunc; eqs.append('trunc')
        n += 1
    assert sorted(eqs) == ['anti', 'trunc']
    print(f"({a},{b}) p={p} q={q}: {n} sign matrices, replay OK, min s_J/need (J<b) = {float(minr):.4f}")
    sys.stdout.flush()
if __name__ == "__main__":
    for (a, b, p, q) in [(3, 1, 5, 3), (3, 1, 3, 5), (1, 3, 5, 3), (3, 3, 5, 3), (3, 3, 3, 5), (3, 3, 7, 3), (3, 3, 3, 7),
                         (4, 2, 5, 3), (4, 2, 3, 5), (4, 2, 7, 3), (4, 2, 3, 7), (2, 2, 5, 3), (2, 4, 3, 5)]:
        run(a, b, p, q)
