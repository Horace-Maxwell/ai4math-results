"""Item 4 + regimes of item 5.
 (a) Anti-checkerboard: if c_j = (-1)^{j+1} s_2 for J < j <= b (b even) then zeta_J = (-1)^J mu_{b-2-J} s_2 (exact), J = b-1..0.
     Parity remark: the induction is parity-independent (checked for odd b too); b even is used only to make the
     anti-checkerboard corner Y_2b = -1 (admissible), i.e. c_b = -s_2.
 (b) B-chain: if c_b = B and c_j = (-1)^j B for J' < j < b then zeta_j = (-1)^{j+1} mu_{b-2-j} B, and chain cells vanish,
     s_j = chat_j Delta(B).
 (c) Lemma M facts: mu_j - L = (-1/q)^{j+1}(1-L); even j: mu_0 <= mu_j < L increasing; odd j: L < mu_j <= mu_1 decreasing;
     mu_0 = (Q-1)/q, mu_1 = (Q^2+1)/q^2.
 (d) Regimes of FD1 at the TRUE mu values for b even up to 40, all 0 <= J < b:
     R0 (J=0): mu = 1, m = mu_{b-2} in [mu0, L), rho = (Q-m)/q.
     R1 (J=b-1): m = 1, mu = mu_{b-2} in [mu0, L), rho = (Q-mu)/q.
     R2a (1<=J<=b-2, J even): mu in (L, mu1], m in [mu0, L), rho < mu.
     R2b (1<=J<=b-2, J odd):  mu in [mu0, L), m in (L, mu1], rho < m.
 (e) FD2 parameter claims (b even): mu_{b-2} in [mu0,L); rho = (Q - mu_{b-2})/q; for b>=4: mu_{b-3} in (L, mu1], mu_{b-4} in [mu0, L).
"""
import sys, random
from fractions import Fraction as Fr
from rv_common import *

out = []
def log(s):
    print(s); sys.stdout.flush(); out.append(s)

qs = [Fr(3), Fr(5), Fr(7), Fr(7, 2), Fr(9, 2), Fr(11), Fr(101), Fr(13, 4)]
Bt = TYPES['B']
# (a)
n = 0
for q in qs:
    Q = q - 1
    for b in range(2, 41, 2):
        mu = pot(b + 2, q)
        for J in range(b - 1, -1, -1):
            cols = {j: scal((-1) ** (j + 1), S2) for j in range(J + 1, b + 1)}
            zeta = tuple(Fr(v) for v in cols[b])
            for j in range(b - 1, J, -1):
                zeta = tuple((zeta[k] + Q * cols[j][k]) / q for k in range(3))
            # now zeta = zeta_J
            assert zeta == scal((-1) ** J * mu[b - 2 - J], S2), (q, b, J)
            n += 1
log(f"(a) anti-checkerboard state zeta_J = (-1)^J mu_(b-2-J) s_2: {n} exact cases (b even <= 40, 8 values of q) OK")
# parity remark: the induction itself is parity-independent (it also holds for odd b); b even is what makes the
# anti-checkerboard's last column c_b = (-1)^(b+1) s_2 = -s_2 admissible (Y_2b = -1).  Check both facts.
holds_odd = 0
for q in qs[:3]:
    Q = q - 1
    for b in range(3, 12, 2):
        mu = pot(b + 2, q)
        J = b - 2
        cols = {j: scal((-1) ** (j + 1), S2) for j in range(J + 1, b + 1)}
        assert cols[b][2] == +1          # for odd b the anti-checkerboard corner is +1: not admissible
        zeta = tuple(Fr(v) for v in cols[b])
        for j in range(b - 1, J, -1):
            zeta = tuple((zeta[k] + Q * cols[j][k]) / q for k in range(3))
        if zeta == scal((-1) ** J * mu[b - 2 - J], S2):
            holds_odd += 1
for b in range(2, 41, 2):
    assert scal((-1) ** (b + 1), S2)[2] == -1   # b even: c_b = -s_2 has corner -1 (admissible)
log(f"    parity: state formula also holds for odd b ({holds_odd}/15 cases) but then the anti-checkerboard corner is +1 "
    f"(inadmissible); for even b the corner is -1.  => b even is used for admissibility of c_b = -s_2, not in the induction.")

# (b) B-chain
n = 0
for q in qs:
    Q = q - 1
    for pp in (3, 5, Fr(11, 2)):
        p = Fr(pp); P = p - 1; M = T(2, p)
        for b in range(2, 31, 2):
            mu = pot(b + 2, q)
            zeta = tuple(Fr(v) for v in Bt)  # zeta_{b-1} = c_b = B
            for j in range(b - 1, -1, -1):
                assert zeta == scal((-1) ** (j + 1) * mu[b - 2 - j], Bt), (q, b, j)
                c = scal((-1) ** j, Bt)
                A = matvec(M, c); Bv = matvec(M, zeta)
                cells = [hcell(Q, mu[j - 1], A[i], Bv[i]) for i in range(3)]
                assert all(x == 0 for x in cells), ("chain cell nonzero", q, pp, b, j, cells)
                zeta = tuple((zeta[k] + Q * c[k]) / q for k in range(3))
                n += 1
            # zeta_{-1} = rho * B and (M zeta_{-1})_2 = rho (p^2-2) > 0  (kappa = 0 for the full chain)
            assert zeta == scal(mu[b - 1], Bt) and matvec(M, zeta)[2] > 0
log(f"(b) B-chain states zeta_j = (-1)^(j+1) mu_(b-2-j) B, all chain cells = 0, full-chain kappa = 0: {n} exact steps OK")

# (c) Lemma M
for q in qs:
    Q = q - 1
    L = Q / (q + 1)
    mu = pot(60, q)
    for j in range(-1, 60):
        assert mu[j] - L == (Fr(-1) / q) ** (j + 1) * (1 - L)
    assert mu[0] == (Q - 1) / q and mu[1] == (Q * Q + 1) / q ** 2
    ev = [mu[j] for j in range(0, 60, 2)]; od = [mu[j] for j in range(1, 60, 2)]
    assert all(ev[i] < ev[i + 1] for i in range(len(ev) - 1)) and all(x < L for x in ev) and ev[0] == mu[0]
    assert all(od[i] > od[i + 1] for i in range(len(od) - 1)) and all(x > L for x in od) and od[0] == mu[1]
    assert all(0 < mu[j] <= 1 for j in range(-1, 60))
log("(c) Lemma M facts (mu_j - L = (-1/q)^(j+1)(1-L), parity monotonicity, mu_0, mu_1): OK")

# (d) regimes
counts = {'R0': 0, 'R1': 0, 'R2a': 0, 'R2b': 0}
for q in qs:
    Q = q - 1; L = Q / (q + 1)
    for b in range(2, 41, 2):
        mu = pot(b + 2, q); mu0, mu1 = mu[0], mu[1]; rho = mu[b - 1]
        for J in range(0, b):
            MU = mu[J - 1]; m = mu[b - 2 - J]
            if J == 0:
                assert MU == 1 and mu0 <= m < L and rho == (Q - m) / q; counts['R0'] += 1
            elif J == b - 1:
                assert m == 1 and mu0 <= MU < L and rho == (Q - MU) / q; counts['R1'] += 1
            elif J % 2 == 0:
                assert L < MU <= mu1 and mu0 <= m < L and rho < MU; counts['R2a'] += 1
            else:
                assert mu0 <= MU < L and L < m <= mu1 and rho < m; counts['R2b'] += 1
            # the odd one of (J-1, b-2-J) is < b-1 (so rho < it) when 1 <= J <= b-2:
            if 1 <= J <= b - 2:
                assert (J - 1) + (b - 2 - J) == b - 3
log(f"(d) FD1 regimes at the true mu-values (b even <= 40, 8 q's): {counts} all OK")

# (e) FD2 parameters
for q in qs:
    Q = q - 1; L = Q / (q + 1)
    for b in range(2, 41, 2):
        mu = pot(b + 2, q)
        assert mu[0] <= mu[b - 2] < L and mu[b - 1] == (Q - mu[b - 2]) / q
        if b >= 4:
            assert L < mu[b - 3] <= mu[1] and mu[0] <= mu[b - 4] < L
log("(e) FD2 parameter claims (mu_(b-2) in [mu0,L), rho=(Q-mu_(b-2))/q, mu_(b-3) in (L,mu1], mu_(b-4) in [mu0,L)): OK")
log("DONE")
