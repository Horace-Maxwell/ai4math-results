"""Item 7: Lemma EQ, the final case analysis and the equality characterisation.

 (a) Full replay of the proof of Theorem B' on EVERY sign matrix (Y_2b = -1) of shapes (2,2), (2,4), for 14 parameter pairs
     (incl. the boundary pairs P=4,Q=2 / P=2,Q=4 and non-integers): c_b in {-s2, C, -E, B}; J; case (i) J<b: state formula,
     s_J > 2 delta_p rho, all other s_j >= 0, kappa >= 0; case (ii) J=b: C -> gap = sum s_j + kappa, -E -> gap > 0,
     B -> sum s_j + kappa > 4P rho; equality set == {Y-, Y+}.
 (b) Lemma EQ for general b (exact, b even up to 40): along Y+, at each column j < b, given the state zeta_j produced by
     columns j+1..b of Y+, the ONLY column c in {+-1}^3 with s_j(c, zeta_j) = 0 is Y+'s column (so s_j = 0 for all j forces
     Y = Y+, independently of the written argument); the strict sign patterns claimed in the proof; kappa(Y+) = 0,
     kappa(Y-) = 2 rho delta_p; all cells of Y+ and Y- vanish.
 (c) The zero set of h stated in PROOF.md §0 ("for A != 0: h(A,B) = 0 <=> -Q|A| <= B sgn A <= 0"): counterexamples, and a check
     that in Lemma EQ's use (type-A columns, states in the cube, mu in [mu0,1]) the extra zeros B sgnA = Q|A|/mu never occur.
"""
import itertools, sys
from fractions import Fraction as Fr
from rv_common import *

out = []
def log(s):
    print(s); sys.stdout.flush(); out.append(s)

ALLC = list(itertools.product((1, -1), repeat=3))
Cc = TYPES['C']; Ec = TYPES['E']; Bc = TYPES['B']


def decompose(Y, p, q, M, mu, Dp, dp):
    b = len(Y[0]) - 1
    Q = q - 1
    cols = [tuple(Y[i][j] for i in range(3)) for j in range(b + 1)]
    zeta = {b - 1: tuple(Fr(v) for v in cols[b])}
    for j in range(b - 1, -1, -1):
        zeta[j - 1] = tuple((zeta[j][k] + Q * cols[j][k]) / q for k in range(3))
    s = []
    for j in range(b):
        A = matvec(M, cols[j]); B = matvec(M, zeta[j])
        s.append(Q * (1 + mu[j - 1]) / q * (Dp - l1(A)) - sum(hcell(Q, mu[j - 1], A[i], B[i]) for i in range(3)) / q)
    kappa = 2 * max(Fr(0), -matvec(M, zeta[-1])[2])
    return cols, zeta, s, kappa


# (a)
pairs = [(5, 3), (3, 5), (7, 3), (3, 7), (5, 7), (7, 5), (13, 11), (101, 3), (3, 101), (Fr(11, 2), Fr(7, 2)), (3, Fr(9, 2)),
         (Fr(5), Fr(3)), (Fr(3), Fr(5)), (Fr(51, 10), Fr(31, 10))]
for b in (2, 4):
    tot = 0
    for (pp, qq) in pairs:
        p = Fr(pp); q = Fr(qq); P = p - 1; Q = q - 1
        M = T(2, p); N = T(b, q); mu = pot(b + 1, q); rho = mu[b - 1]
        Dp = d_def(2, p); dp = delta_def(2, p); need = 2 * dp * rho
        Th = Theta(2, b, p, q)
        Ym, Yp = Yminus(2, b), Yplus(2, b)
        eq = []
        cnt = {'i': 0, 'C': 0, '-E': 0, 'B': 0, 'anti': 0}
        for bits in itertools.product((1, -1), repeat=3 * (b + 1) - 1):
            Y = [list(bits[0:b + 1]), list(bits[b + 1:2 * b + 2]), list(bits[2 * b + 2:]) + [-1]]
            cols, zeta, s, kappa = decompose(Y, p, q, M, mu, Dp, dp)
            gap = Th - G(Y, p, q, M, N)
            Delta_b = Dp - l1(matvec(M, cols[b]))
            assert gap == q ** b * (sum(s) + rho * Delta_b + kappa - need)
            assert all(x >= 0 for x in s) and kappa >= 0
            assert cols[b] in (neg(S2), Cc, neg(Ec), Bc)
            Jset = [j for j in range(b + 1) if cols[j] != scal((-1) ** (j + 1), S2)]
            if not Jset:
                assert Y == Ym and gap == 0; eq.append('Y-'); cnt['anti'] += 1; continue
            J = max(Jset)
            if J < b:
                assert cols[b] == neg(S2)
                assert zeta[J] == scal((-1) ** J * mu[b - 2 - J], S2)
                assert s[J] > need
                assert gap >= q ** b * (s[J] - need) > 0
                cnt['i'] += 1
            else:
                cb = cols[b]
                if cb == Cc:
                    assert rho * Delta_b == need and gap == q ** b * (sum(s) + kappa)
                    if gap == 0:
                        assert all(x == 0 for x in s) and kappa == 0 and Y == Yp
                        eq.append('Y+')
                    cnt['C'] += 1
                elif cb == neg(Ec):
                    assert Delta_b == 4 * P * P and gap >= q ** b * (4 * P * P - 2 * dp) * rho > 0
                    cnt['-E'] += 1
                else:
                    assert cb == Bc and rho * Delta_b == need - 4 * P * rho
                    assert sum(s) + kappa > 4 * P * rho and gap > 0
                    cnt['B'] += 1
            if gap == 0:
                assert Y in (Ym, Yp)
        assert sorted(eq) == ['Y+', 'Y-'], eq
        tot += sum(cnt.values())
        log(f"(a) (2,{b}) p={p} q={q}: every step holds; equality exactly at Y-, Y+; case counts {cnt}")
    log(f"(a) shape (2,{b}): {tot} sign matrices replayed")

# (b) Lemma EQ for general b
for (pp, qq) in [(5, 3), (3, 5), (7, 3), (3, 7), (101, 3), (3, 101), (Fr(11, 2), Fr(7, 2)), (3, Fr(9, 2))]:
    p = Fr(pp); q = Fr(qq); P = p - 1; Q = q - 1
    M = T(2, p); Dp = d_def(2, p); dp = delta_def(2, p)
    for b in range(2, 41, 2):
        mu = pot(b + 1, q); rho = mu[b - 1]
        Yp = Yplus(2, b); Ym = Yminus(2, b)
        colsP = [tuple(Yp[i][j] for i in range(3)) for j in range(b + 1)]
        assert colsP[b] == Cc and all(colsP[j] == scal((-1) ** j, S2) for j in range(b))
        zeta = tuple(Fr(v) for v in Cc)
        for j in range(b - 1, -1, -1):
            Bv = matvec(M, zeta)
            if j == b - 1:
                assert Bv == [0, -2 * p * P, P * P - 1]
            else:
                sg = Bv[0]
                assert sg != 0 and Bv[1] * sg < 0 and Bv[2] * sg > 0   # strict pattern sigma(+,-,+)
                assert abs(Bv[0]) <= 2 * p * P and abs(Bv[1]) <= 2 * p * P and abs(Bv[2]) <= p * p
            zeros = []
            for c in ALLC:
                A = matvec(M, c)
                sj = Q * (1 + mu[j - 1]) / q * (Dp - l1(A)) - sum(hcell(Q, mu[j - 1], A[i], Bv[i]) for i in range(3)) / q
                assert sj >= 0
                if sj == 0:
                    zeros.append(c)
            assert zeros == [colsP[j]], (pp, qq, b, j, zeros)
            zeta = tuple((zeta[k] + Q * colsP[j][k]) / q for k in range(3))
        # zeta = zeta_{-1} of Y+
        assert matvec(M, zeta)[2] > 0     # kappa(Y+) = 0
        # Y-: cells vanish, kappa = 2 rho delta_p
        colsM = [tuple(Ym[i][j] for i in range(3)) for j in range(b + 1)]
        zeta = tuple(Fr(v) for v in colsM[b])
        for j in range(b - 1, -1, -1):
            A = matvec(M, colsM[j]); Bv = matvec(M, zeta)
            assert all(hcell(Q, mu[j - 1], A[i], Bv[i]) == 0 for i in range(3))
            zeta = tuple((zeta[k] + Q * colsM[j][k]) / q for k in range(3))
        assert zeta == scal(-rho, S2) and 2 * max(Fr(0), -matvec(M, zeta)[2]) == 2 * rho * dp
log("(b) Lemma EQ, b even <= 40, 8 parameter pairs: along Y+ the column with s_j = 0 is unique and equals Y+'s column at every "
    "j < b; strict sign patterns as claimed; kappa(Y+) = 0; Y- has all cells 0 and kappa = 2 rho delta_p: OK")

# (c) zero set of h
Q = Fr(2)
cex = []
for mu in (Fr(1), Fr(1, 2), Fr(3, 5)):
    A = Fr(1); B = Q * A / mu
    cex.append((mu, A, B, hcell(Q, mu, A, B)))
log("(c) PROOF.md §0 claims: for A != 0, h(A,B) = 0 <=> -Q|A| <= B sgn A <= 0.  Counterexamples (Q=2, h = 0 with B sgnA > 0): "
    + "; ".join(f"mu={m_}, A={a_}, B={b_}: h={h_}" for (m_, a_, b_, h_) in cex))
# for mu = 0 the whole ray B < -QA is also a zero set
log(f"    and for mu = 0: h(1, -5) = {hcell(Q, Fr(0), Fr(1), Fr(-5))} although -5 < -Q.  Correct statement (A>0, mu>0): "
    f"h = 0 iff B in [-QA, 0] or B = QA/mu.")
# in Lemma EQ's use: type-A column, |B_i| <= max over cube < Q|A_i| <= Q|A_i|/mu, so the extra zero never occurs
ok = True
for pp in (3, 5, 7, Fr(11, 2), 101):
    for qq in (3, 5, 7, Fr(9, 2), 101):
        p = Fr(pp); q = Fr(qq); P = p - 1; Q = q - 1
        if not ((P >= 4 and Q >= 2) or (P == 2 and Q >= 4)):
            continue
        a = [2 * p * P, 2 * P * P, P * P + 1]; mx = [2 * p * P, 2 * p * P, p * p]
        ok &= all(mx[i] < Q * a[i] for i in range(3))
log(f"    in Lemma EQ (type-A columns): max_cube |B_i| < Q|A_i| for i=0,1,2 on the parameter range: {ok} "
    f"=> the extra zeros are unreachable, so the use of the characterisation is harmless.")
log("DONE")
