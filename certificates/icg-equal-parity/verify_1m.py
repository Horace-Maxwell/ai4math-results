"""Exact (Fraction) verification of every step of the proof for exponent pairs (1,m), m odd (PROOF.md, Part A).

Notation: x = prime with exponent m (path base), P = x-1, R = r-1 where r = other prime (exponent 1).
u = row 0, v = row 1 of the sign matrix Y (v_m = -1), w1 = u - v, w2 = R u + v.
Phi(u,v) = R N(w1) + N(w2) - 2 (z_{-1}(w2))^-  equals G(Y)/x^m (reduction, checked against the matrix model).
Steps checked for every (u,v):
 (S0) reduction Phi = G(Y)/x^m                       [matrix model, exact]
 (S1) potential identity N(w) = sum_k chat_k |w_k| + (1/x) sum_{k<m} h(w_k, z_k(w))  (real w)
 (S2) h(w2_k, z_k(w2)) <= 0; h(w1_k,.) <= 0 on D; h(0,B) = 2 mu |B| on E
 (S3) case I   (m in E): every E-surplus >= 0 and inequality
      case II  (m in D, E nonempty): some E position k0 has surplus_k0 (+ D-term at k0+1 in the refined x=3 case) >= 2(R-1)rho
      case III (E empty, v=-u): Lemma B (u_0=u_m): sigma(u) >= mu_J mu_{m-2-J} >= mu_0 mu_{m-2}, and (3R-1) mu_0 mu_{m-2} > (R-1) rho;
                                Lemma C (u_0=-u_m): rho - r_{-1}(u) <= sum_{j in NA, j>=1, neg} 2 mu_{m-2-j} x^{-(j+1)} and termwise bound
 (S4) Phi <= target with equality iff (u,v) is the anti-checkerboard or truncated checkerboard.
"""
import itertools, sys
from fractions import Fraction as Fr
from core import T, Gval, dfun, delta_last, path


def mus(m, x):
    mu = {-1: Fr(1)}
    for k in range(m):
        mu[k] = (x - 1 - mu[k - 1]) / x
    return mu


def hfun(P, mu, A, B):
    return P * abs(A - B) + mu * abs(B + P * A) - (P - mu) * abs(B) - P * (1 + mu) * abs(A)


def Nrm(w, x):
    z = path(w, x)
    m = len(w) - 1
    return abs(z[-1]) + sum(abs(z[k - 1] - z[k]) for k in range(m))


def sigma(y, x, mu):
    z = path(y, x)
    m = len(y) - 1
    return sum(mu[j] * abs(z[j]) for j in range(m) if y[j] == y[j + 1])


def run(m, x, R, check_model=False, p_prime=None):
    x = Fr(x); R = Fr(R); P = x - 1
    mu = mus(m, x)
    rho = mu[m - 1]
    c = {k: P * (1 + mu[k - 1]) / x for k in range(m)}
    chat = dict(c); chat[m] = rho
    Dh = sum(chat.values())
    assert Dh == dfun(m, x) / x ** m
    assert rho == delta_last(m, x) / x ** m
    tgt = (3 * R - 1) * Dh - 2 * (R - 1) * rho
    s = [(-1) ** i for i in range(m + 1)]
    anti = (tuple(-t for t in s), tuple(s))
    trunc = (tuple(s), tuple(-t for t in s[:m]) + (-1,))
    N = T(m, x) if check_model else None
    maxphi = None; eqset = []
    stats = {'I': 0, 'II': 0, 'II_refined': 0, 'IIIa': 0, 'IIIb': 0}
    for bits in itertools.product([1, -1], repeat=2 * (m + 1)):
        u = bits[:m + 1]; v = bits[m + 1:]
        if v[m] != -1:
            continue
        w1 = [u[i] - v[i] for i in range(m + 1)]
        w2 = [R * u[i] + v[i] for i in range(m + 1)]
        z1 = path(w1, x); z2 = path(w2, x)
        phi = R * Nrm(w1, x) + Nrm(w2, x) - 2 * max(Fr(0), -z2[-1])
        # (S0)
        if check_model:
            Y = [list(u), list(v)]
            g = Gval(Y, p_prime, x)
            assert g == phi * x ** m, ("S0", m, x, R, u, v)
        # (S1)
        for w, z in ((w1, z1), (w2, z2)):
            lhs = Nrm(w, x)
            rhs = sum(chat[k] * abs(w[k]) for k in range(m + 1)) + sum(hfun(P, mu[k - 1], w[k], z[k]) for k in range(m)) / x
            assert lhs == rhs, ("S1", w)
        E = [k for k in range(m + 1) if u[k] == v[k]]
        D = [k for k in range(m + 1) if u[k] != v[k]]
        # (S2)
        for k in range(m):
            assert hfun(P, mu[k - 1], w2[k], z2[k]) <= 0, ("S2 w2", u, v, k)
            h1 = hfun(P, mu[k - 1], w1[k], z1[k])
            if k in D:
                assert h1 <= 0, ("S2 w1 D", u, v, k)
            else:
                assert h1 == 2 * mu[k - 1] * abs(z1[k]), ("S2 w1 E", u, v, k)
        # decomposition
        H = sum(R * hfun(P, mu[k - 1], w1[k], z1[k]) + hfun(P, mu[k - 1], w2[k], z2[k]) for k in range(m)) / x
        assert phi == (3 * R - 1) * Dh - 2 * (R - 1) * sum(chat[k] for k in E) + H - 2 * max(Fr(0), -z2[-1]), "decomp"
        surplus = {k: 2 * (R - 1) * c[k] - (2 * R / x) * mu[k - 1] * abs(z1[k]) for k in E if k < m}
        Dterm = {k: -(R / x) * hfun(P, mu[k - 1], w1[k], z1[k]) for k in D if k < m}
        # (S3)
        if m in E:
            stats['I'] += 1
            assert all(sv >= 0 for sv in surplus.values())
        elif E:
            stats['II'] += 1
            assert u[m] == 1
            ok = any(sv >= 2 * (R - 1) * rho for sv in surplus.values())
            if not ok:
                # refined argument (x=3): E = {0}, position 1 is D with NA of u at 1
                assert x == 3 and set(E) == {0}, ("II fails", m, x, R, u, v)
                stats['II_refined'] += 1
                assert surplus[0] + Dterm.get(1, 0) >= 2 * (R - 1) * rho, ("II refined fails", u, v)
                assert u[1] == u[2] if m >= 2 else True
        else:
            assert all(v[i] == -u[i] for i in range(m + 1)) and u[m] == 1
            sg = sigma(u, x, mu)
            zu = path(u, x)
            if u[0] == 1:
                stats['IIIa'] += 1
                NA = [j for j in range(m) if u[j] == u[j + 1]]
                J = max(NA)
                assert sg >= mu[J] * abs(zu[J]) and abs(zu[J]) == mu[m - 2 - J]
                if m >= 3:
                    assert mu[J] * mu[m - 2 - J] >= mu[0] * mu[m - 2]
                    assert (3 * R - 1) * mu[0] * mu[m - 2] > (R - 1) * rho
                else:
                    assert (3 * R - 1) * mu[0] > (R - 1) * rho
                assert 2 * (3 * R - 1) * sg > 2 * (R - 1) * rho
            else:
                stats['IIIb'] += 1
                NA = [j for j in range(m) if u[j] == u[j + 1]]
                # deviation formula d_{-1} = sum_{j in NA} 2 r^alt_j x^{-(j+1)} prod_{i<j} eps_i
                eps = [1 if u[i] == u[i + 1] else -1 for i in range(m)]
                d = Fr(0); bound = Fr(0)
                for j in NA:
                    pr = 1
                    for i in range(j):
                        pr *= eps[i]
                    d += 2 * mu[m - 2 - j] / x ** (j + 1) * pr
                    if pr < 0:
                        assert j >= 1
                        bound += 2 * mu[m - 2 - j] / x ** (j + 1)
                assert abs(zu[-1]) - rho == d, "deviation formula"
                assert rho - abs(zu[-1]) <= bound
                for j in NA:
                    if j >= 1:
                        assert 2 * (R - 1) * mu[m - 2 - j] / x ** (j + 1) <= (3 * R - 1) * mu[j] * abs(zu[j])
                assert (3 * R - 1) * sg >= (R - 1) * (rho - abs(zu[-1]))
                if NA:
                    assert (3 * R - 1) * sg > (R - 1) * (rho - abs(zu[-1]))
        # (S4)
        assert phi <= tgt, ("S4", u, v)
        if phi == tgt:
            eqset.append((tuple(u), tuple(v)))
    assert sorted(eqset) == sorted([anti, trunc]), ("equality set", eqset)
    return stats


if __name__ == "__main__":
    cases = []
    for m in [1, 3, 5, 7]:
        for (x, R) in [(3, 4), (3, 6), (3, 10), (3, 12), (3, Fr(9, 2)), (5, 2), (5, 4), (5, 6), (7, 2), (7, 4), (11, 2), (11, 12),
                       (13, 16), (Fr(11, 2), 2), (6, 2), (5, Fr(5, 2)), (3, 40), (29, 2)]:
            cases.append((m, x, R))
    for (m, x, R) in cases:
        st = run(m, x, R)
        print(f"m={m} x={x} R={R}: all steps verified exactly; case counts {st}")
        sys.stdout.flush()
    # model cross-check (S0) with actual primes: r = R+1 prime, x prime
    for (m, x, r) in [(1, 3, 5), (3, 3, 5), (3, 5, 3), (3, 3, 7), (5, 3, 5), (3, 7, 3), (5, 5, 3), (3, 11, 5)]:
        st = run(m, x, r - 1, check_model=True, p_prime=r)
        print(f"model check m={m} q={x} p={r}: reduction and all steps verified exactly")
