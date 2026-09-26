"""Referee-2, test 1.  Independent checks (exact) of the foundations used by PROOF.md sec. 11 for general a:
 (1) T_k(x) formula == Ramanujan-sum definition (primes), d_k, delta_k closed forms == matrix values;
 (2) Proposition 1 for a+1 rows:  (Theta - G)/q^b = sum_{j<b} s_j + rho*Delta(c_b) + kappa - 2 delta_a rho,
     s_j computed from the cell DEFINITION at the true column-path state; random Y, a in {3,4} (and 2,5), several b,
     random rational parameters in both regions (P>=4,Q>=2) and (P=2,Q>=4);
 (3) at the true states: s_j >= 0, s_j > 0 for c_j != +-s_a, every cell <= 0 when c_j = +-s_a, kappa >= 0;
 (4) exact anti-checkerboard state zeta_J = (-1)^J mu_{b-2-J} s_a when columns J+1..b agree with Y-;
 (5) Y+ : all cells vanish, kappa = 0, Delta(g_trunc) = 2 delta_a, G(Y+) = G(Y-) = Theta;
 (6) Q delta_a > p^a (used for the EQ forcing) on sample points, and symbolically (sympy) on both regions.
"""
import itertools, random, sys
from fractions import Fraction as Fr
from r2core import (T, T_ram, mus, matvec, l1, svec, dd, de, d_closed, delta_closed, G, Theta, anti, trunc, h,
                    colpath, surplus_direct)

random.seed(20260926)
out = open('logs/t1_prop1.log', 'w')
def log(*a):
    s = ' '.join(str(x) for x in a); print(s); out.write(s + '\n'); out.flush()

# (1)
for x in (3, 5, 7, 11, 13):
    for k in range(1, 8):
        assert T(k, x) == [[Fr(v) for v in row] for row in T_ram(k, x)], (k, x)
for x in (Fr(3), Fr(5), Fr(7), Fr(11, 2), Fr(7, 2), Fr(101), Fr(13, 3)):
    for k in range(1, 10):
        assert dd(k, x) == d_closed(k, x) and de(k, x) == delta_closed(k, x), (k, x)
log("(1) T formula == Ramanujan-sum definition (x prime <= 13, k <= 7); d_k, delta_k closed forms == matrix values: OK")

def rand_params(region):
    if region == 'big':
        P = random.choice([Fr(4), Fr(9, 2), Fr(5), Fr(6), Fr(10), Fr(100), Fr(4) + Fr(random.randint(0, 400), 37)])
        Q = random.choice([Fr(2), Fr(5, 2), Fr(4), Fr(6), Fr(100), Fr(2) + Fr(random.randint(0, 400), 29)])
    else:
        P = Fr(2)
        Q = random.choice([Fr(4), Fr(9, 2), Fr(6), Fr(10), Fr(100), Fr(4) + Fr(random.randint(0, 400), 31)])
    return P + 1, Q + 1

def decompose(Y, p, q):
    a, b = len(Y) - 1, len(Y[0]) - 1
    Q = q - 1
    M = T(a, p); N = T(b, q)
    mu = mus(b + 1, q); rho = mu[b - 1]
    Da = dd(a, p); da = de(a, p)
    cols = [[Y[i][j] for i in range(a + 1)] for j in range(b + 1)]
    z = colpath(cols, q)
    s = []; cellinfo = []
    for j in range(b):
        A = matvec(M, cols[j]); B = matvec(M, z[j])
        cells = [h(Q, mu[j - 1], A[i], B[i]) for i in range(a + 1)]
        s.append(Q * (1 + mu[j - 1]) / q * (Da - l1(A)) - sum(cells) / q)
        cellinfo.append(cells)
    kappa = 2 * max(Fr(0), -matvec(M, z[-1])[a])
    Delta_b = Da - l1(matvec(M, cols[b]))
    return dict(M=M, N=N, mu=mu, rho=rho, Da=Da, da=da, cols=cols, z=z, s=s, cells=cellinfo, kappa=kappa, Delta_b=Delta_b)

# (2),(3)
cnt = 0
for a in (2, 3, 4, 5):
    for b in [bb for bb in range(1, 10) if (a + bb) % 2 == 0]:
        for trial in range(60 if a <= 4 else 20):
            region = 'big' if trial % 2 == 0 else 'p3'
            p, q = rand_params(region)
            sa = svec(a)
            # random Y with Y_ab = -1, biased towards near-extremal matrices (random perturbations of Y-/Y+)
            kind = trial % 3
            if kind == 0:
                Y = [[random.choice([1, -1]) for _ in range(b + 1)] for _ in range(a + 1)]
            else:
                Y = [row[:] for row in (anti(a, b) if kind == 1 else trunc(a, b))]
                for _ in range(random.randint(1, 3)):
                    i, j = random.randint(0, a), random.randint(0, b)
                    Y[i][j] = -Y[i][j]
            Y[a][b] = -1
            D = decompose(Y, p, q)
            lhs = (Theta(a, b, p, q) - G(Y, D['M'], D['N'])) / q ** b
            rhs = sum(D['s']) + D['rho'] * D['Delta_b'] + D['kappa'] - 2 * D['da'] * D['rho']
            assert lhs == rhs, (a, b, p, q)
            assert D['kappa'] >= 0
            for j in range(b):
                c = D['cols'][j]
                assert D['s'][j] >= 0, ("S fails", a, b, p, q, j)
                if c != sa and c != [-x for x in sa]:
                    assert D['s'][j] > 0, ("S strict fails", a, b, p, q, j)
                else:
                    assert all(x <= 0 for x in D['cells'][j]), ("alt cell > 0", a, b, p, q, j)
            cnt += 1
log(f"(2)+(3) Proposition 1 identity, s_j >= 0 (strict off +-s_a), alt cells <= 0, kappa >= 0: {cnt} random (Y, p, q), a in 2..5: OK")

# (4) exact anti state, (5) Y+
cnt = 0
for a in (2, 3, 4, 5, 6):
    for b in [bb for bb in range(1, 14) if (a + bb) % 2 == 0]:
        for region in ('big', 'p3'):
            for _ in range(3):
                p, q = rand_params(region)
                Q = q - 1
                mu = mus(b + 2, q)
                sa = svec(a)
                Ym = anti(a, b); Yp = trunc(a, b)
                colsm = [[Ym[i][j] for i in range(a + 1)] for j in range(b + 1)]
                zm = colpath(colsm, q)
                for J in range(b):
                    assert zm[J] == [(-1) ** J * mu[b - 2 - J] * x for x in sa]
                Dp = decompose(Yp, p, q)
                assert all(x == 0 for cells in Dp['cells'] for x in cells), ("Y+ cell nonzero", a, b, p, q)
                assert Dp['kappa'] == 0
                assert Dp['Delta_b'] == 2 * Dp['da']
                th = Theta(a, b, p, q)
                assert G(Yp, Dp['M'], Dp['N']) == th and G(Ym, Dp['M'], Dp['N']) == th
                assert Q * Dp['da'] > p ** a
                # last row of M sums to p^a (used: |(M zeta)_a| <= p^a)
                assert sum(abs(x) for x in Dp['M'][a]) == p ** a
                cnt += 1
log(f"(4)+(5)+(6-numeric) exact anti state, Y+ cells all zero, kappa(Y+)=0, Delta(g_trunc)=2 delta_a, G(Y+)=G(Y-)=Theta, "
    f"Q delta_a > p^a: {cnt} (a,b,p,q) cases, a<=6, b<=13: OK")

# (6) symbolic: Q*delta_a - p^a > 0 on both regions, a = 2..8
import sympy as sp
s_, t_ = sp.symbols('s t', nonnegative=True)
for a in range(2, 9):
    for (Pv, Qv, name) in ((4 + s_, 2 + t_, 'big'), (sp.Integer(2), 4 + t_, 'p3')):
        pv = Pv + 1
        expr = sp.expand(Qv * (pv ** a * Pv + 2 * (-1) ** a) - pv ** a * (pv + 1))   # (p+1)(Q delta_a - p^a)
        poly = sp.Poly(expr, s_, t_)
        assert all(c >= 0 for c in poly.coeffs()) and poly.coeff_monomial(1) > 0, (a, name, expr)
log("(6) (p+1)(Q delta_a - p^a) has nonnegative coefficients and positive constant term after P=4+s,Q=2+t / P=2,Q=4+t, a=2..8: OK")
