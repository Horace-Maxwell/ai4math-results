"""Item 2 (and basic facts of item 1/§0-§1).
 (a) T_k(x) from the note.tex definition == Ramanujan-sum formula phi(x^{k-i}) c_{x^{k-j}}(x^i) (prime x, k<=6).
 (b) d_k, delta_k: definition ||T s||_1, (T s)_k  == closed forms; D_p = 5P^2+2P+1, delta_p = P^2+1; M = T_2(p) form.
 (c) the type table alpha(t) = M t, F_p, Delta; max |(Mc)_i| over {+-1}^3.
 (d) Lemma P (potential identity) for random real w (rational), b <= 10.
 (e) Proposition 1: (Theta - G)/q^b == sum_{j<b} s_j + rho*Delta(c_b) + kappa - 2 delta_p rho, derived here from scratch
     (row paths of MY, column-path states zeta_j), for EVERY Y with Y_{2b}=-1 in shapes (2,2),(2,4), many (p,q) incl.
     non-integers and parameters outside the theorem's range (the identity is unconditional); random Y for b = 6..12.
     Also checks z_j(r_i) == (M zeta_j)_i and zeta_j in [-1,1]^3.
"""
import itertools, random, sys
from fractions import Fraction as Fr
from rv_common import *

random.seed(20260926)
out = []
def log(s):
    print(s); sys.stdout.flush(); out.append(s)

# (a)
for k in range(1, 7):
    for x in (3, 5, 7):
        assert T(k, x) == T_ramanujan(k, x), (k, x)
log("(a) T_k(x) definition == Ramanujan-sum formula for k=1..6, x in {3,5,7}: OK")

# (b)
for k in range(0, 12):
    for x in (3, 5, 7, Fr(7, 2), Fr(10, 3), 11, 101):
        assert d_def(k, x) == d_closed(k, x), (k, x)
        if k >= 1:
            assert delta_def(k, x) == delta_closed(k, x), (k, x)
            mu = pot(k, x)
            assert delta_def(k, x) == Fr(x) ** k * mu[k - 1]
            chat_sum = sum((Fr(x) - 1) * (1 + mu[j - 1]) / x for j in range(k)) + mu[k - 1]
            assert d_def(k, x) == Fr(x) ** k * chat_sum
for pp in (3, 5, 7, Fr(11, 2), 13, 101):
    P = Fr(pp) - 1
    assert T(2, pp) == [[0, -pp * P, pp * P], [-pp * P, P * P, P], [pp * P, P, 1]]
    assert d_def(2, pp) == 5 * P * P + 2 * P + 1 == 5 * Fr(pp) ** 2 - 8 * pp + 4
    assert delta_def(2, pp) == P * P + 1 == Fr(pp) ** 2 - 2 * pp + 2
log("(b) d_k, delta_k definitions == closed forms (k<=11); x^k mu_{k-1} = delta_k; d_k = x^k (sum c_j + mu_{k-1}); "
    "T_2(p), D_p = 5P^2+2P+1 = 5p^2-8p+4, delta_p = P^2+1 = p^2-2p+2: OK")

# (c)
for pp in (3, 5, 7, Fr(11, 2), Fr(9, 2), 13, 101):
    p = Fr(pp); P = p - 1
    M = T(2, p)
    Dp = d_def(2, p)
    exp_alpha = {'A': (2 * p * P, -2 * P * P, P * P + 1), 'B': (-2 * p * P, -2 * P, p * p - 2),
                 'C': (0, -2 * p * P, P * P - 1), 'E': (0, 0, p * p)}
    exp_F = {'A': Dp, 'B': 3 * p * p - 4, 'C': 3 * p * p - 4 * p, 'E': p * p}
    exp_D = {'A': 0, 'B': 2 * (P - 1) ** 2, 'C': 2 * (P * P + 1), 'E': 4 * P * P}
    for t, c in TYPES.items():
        a = tuple(matvec(M, c))
        assert a == exp_alpha[t], (t, a)
        assert l1(a) == exp_F[t] and Dp - l1(a) == exp_D[t]
    allc = list(itertools.product((1, -1), repeat=3))
    mx = [max(abs(matvec(M, c)[i]) for c in allc) for i in range(3)]
    assert mx == [2 * p * P, 2 * p * P, p * p], mx
    assert Dp - l1(matvec(M, (1, 1, -1))) == 2 * (P * P + 1) - 4 * P
log("(c) type table alpha(t), F_p(t), Delta(t) and max|(Mc)_i| = (2pP, 2pP, p^2): OK (7 values of p incl. non-integer)")

# (d) Lemma P for random real w
cnt = 0
for trial in range(3000):
    b = random.randint(1, 10)
    q = random.choice([Fr(3), Fr(5), Fr(7), Fr(7, 2), Fr(13, 3), Fr(101)])
    Q = q - 1
    w = [Fr(random.randint(-60, 60), random.randint(1, 9)) for _ in range(b + 1)]
    if trial % 3 == 0:
        w = [random.choice([-1, 0, 1, 2, -2]) * Fr(random.randint(1, 5)) for _ in range(b + 1)]
    mu = pot(b, q)
    z = path(w, q)
    nu = l1(matvec(T(b, q), w)) / q ** b
    chat = [Q * (1 + mu[j - 1]) / q for j in range(b)] + [mu[b - 1]]
    rhs = sum(chat[j] * abs(w[j]) for j in range(b + 1)) + sum(hcell(Q, mu[j - 1], w[j], z[j]) for j in range(b)) / q
    assert nu == rhs
    # path lemma and last coordinate
    assert matvec(T(b, q), w)[b] == q ** b * z[-1]
    cnt += 1
log(f"(d) Lemma P (nu(w) = sum chat_j|w_j| + (1/q) sum h_{{mu_(j-1)}}(w_j, z_j(w))) and (T_b w)_b = q^b z_-1: {cnt} random exact cases OK")


# (e) Proposition 1
def prop1_terms(Y, p, q, M, mu):
    b = len(Y[0]) - 1
    p = Fr(p); q = Fr(q); Q = q - 1
    Dp = d_def(2, p); dp = delta_def(2, p); rho = mu[b - 1]
    cols = [tuple(Y[i][j] for i in range(3)) for j in range(b + 1)]
    # rows of MY and their q-paths
    MY = matmul(M, Y)
    zr = [path(MY[i], q) for i in range(3)]
    # column-path states
    zeta = {b - 1: tuple(Fr(v) for v in cols[b])}
    for j in range(b - 1, -1, -1):
        zeta[j - 1] = tuple((zeta[j][k] + Q * cols[j][k]) / q for k in range(3))
    for j in range(-1, b):
        Mz = matvec(M, zeta[j])
        assert all(zr[i][j] == Mz[i] for i in range(3)), "z_j(r_i) != (M zeta_j)_i"
        assert all(-1 <= v <= 1 for v in zeta[j])
    Delta = lambda c: Dp - l1(matvec(M, c))
    s = []
    for j in range(b):
        A = matvec(M, cols[j]); B = matvec(M, zeta[j])
        chat = Q * (1 + mu[j - 1]) / q
        s.append(chat * Delta(cols[j]) - sum(hcell(Q, mu[j - 1], A[i], B[i]) for i in range(3)) / q)
    kappa = 2 * max(Fr(0), -zr[2][-1])
    return s, rho * Delta(cols[b]), kappa, 2 * dp * rho


pairs = [(5, 3), (3, 5), (7, 3), (3, 7), (5, 7), (7, 5), (11, 13), (Fr(11, 2), Fr(7, 2)), (3, Fr(9, 2)), (101, 3), (3, 101),
         (Fr(4), Fr(3)), (Fr(5, 2), Fr(5, 2))]   # last two: outside the theorem's range (identity is unconditional)
for b in (2, 4):
    for (p, q) in pairs:
        p = Fr(p); q = Fr(q)
        M = T(2, p); N = T(b, q); mu = pot(b + 1, q)
        Th = Theta(2, b, p, q)
        n = 0
        for bits in itertools.product((1, -1), repeat=3 * (b + 1) - 1):
            Y = [list(bits[0:b + 1]), list(bits[b + 1:2 * b + 2]), list(bits[2 * b + 2:]) + [-1]]
            s, sb, kappa, need = prop1_terms(Y, p, q, M, mu)
            gap = Th - G(Y, p, q, M, N)
            assert gap == q ** b * (sum(s) + sb + kappa - need), ("Prop 1 fails", b, p, q, Y)
            n += 1
        log(f"(e) Prop 1 exact for all {n} Y, shape (2,{b}), (p,q)=({p},{q})")
cnt = 0
for b in (6, 8, 10, 12):
    for (p, q) in [(5, 3), (3, 5), (Fr(23, 4), Fr(17, 5)), (3, Fr(31, 6)), (13, 3)]:
        p = Fr(p); q = Fr(q)
        M = T(2, p); N = T(b, q); mu = pot(b + 1, q); Th = Theta(2, b, p, q)
        for trial in range(60):
            Y = [[random.choice((1, -1)) for _ in range(b + 1)] for _ in range(3)]
            Y[2][b] = -1
            s, sb, kappa, need = prop1_terms(Y, p, q, M, mu)
            assert Th - G(Y, p, q, M, N) == q ** b * (sum(s) + sb + kappa - need)
            cnt += 1
log(f"(e) Prop 1 exact for {cnt} random Y with b in {{6,8,10,12}}")
log("ALL OK")
