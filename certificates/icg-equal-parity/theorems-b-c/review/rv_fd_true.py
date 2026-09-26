"""Items 5-6 at the TRUE parameter values, directly from the definitions (no closed forms), plus a dense-grid test of the
vertex reduction.

 (A) FD1: for b even <= 40, every J < b, every column c != -eps s_2: build the actual state zeta_J by the recursion from the
     anti-checkerboard tail and compute s_J from the cell definition; check s_J > 2 delta_p rho.  Report min ratio.
 (B) FD2(a): c_b = B, every c_{b-1} (8 columns): s_{b-1} vs 4P rho.  P>=4: all 8 columns must pay; P=2: the 7 non-chain ones.
 (C) FD2(b), P = 2: chain c_j = (-1)^j B for J' < j <= b, deviation at J' (7 columns) or J' = -1 (full chain, kappa included);
     check chain cost + s_J' (+kappa for J'=-1) > 8 rho, for every J'.  Also the k >= 3 claim: the chain cost of the three
     columns b-1, b-2, b-3 alone exceeds 8 rho.
 (D) Dense exact grid over the relaxed parameter boxes (R0,R1,R2a,R2b for FD1; FD2 (a),(b) k=1,2): the relaxed function is
     positive everywhere on the grid, and its grid minimum is >= its vertex minimum (consistent with separate concavity).
"""
import sys, itertools
from fractions import Fraction as Fr
from rv_common import *

out = []
def log(s):
    print(s); sys.stdout.flush(); out.append(s)

ALLC = list(itertools.product((1, -1), repeat=3))


def s_at(M, Q, mu_prev, c, zeta, Dp):
    q = Q + 1
    A = matvec(M, c); B = matvec(M, zeta)
    return Q * (1 + mu_prev) / q * (Dp - l1(A)) - sum(hcell(Q, mu_prev, A[i], B[i]) for i in range(3)) / q


pairs = [(5, 3), (7, 3), (11, 3), (101, 3), (1009, 3), (3, 5), (3, 7), (3, 11), (3, 101), (3, 1009), (5, 7), (7, 5),
         (13, 17), (17, 13), (Fr(5), Fr(3)), (Fr(21, 4), Fr(3)), (Fr(5), Fr(31, 10)), (Fr(3), Fr(5)), (Fr(3), Fr(51, 10)),
         (Fr(41, 2), Fr(17, 5))]
bs = list(range(2, 41, 2))

# (A)
worstA = None; nA = 0
per_dev_worst = {}
for (pp, qq) in pairs:
    p = Fr(pp); q = Fr(qq); P = p - 1; Q = q - 1
    M = T(2, p); Dp = d_def(2, p); dp = delta_def(2, p)
    for b in bs:
        mu = pot(b + 2, q); rho = mu[b - 1]; need = 2 * dp * rho
        for J in range(b):
            eps = (-1) ** J
            zeta = tuple(Fr(v) for v in scal((-1) ** (b + 1), S2))
            for j in range(b - 1, J, -1):
                c = scal((-1) ** (j + 1), S2)
                zeta = tuple((zeta[k] + Q * c[k]) / q for k in range(3))
            for c in ALLC:
                if c == scal(-eps, S2):
                    continue
                sJ = s_at(M, Q, mu[J - 1], c, zeta, Dp)
                nA += 1
                r = sJ / need
                assert r > 1, ("FD1 FAILS", pp, qq, b, J, c, r)
                key = next(k for k, v in TYPES.items() if v == c or neg(v) == c) + ('same' if (c == scal(eps, TYPES['A']) or c == scal(eps, TYPES['B']) or c == scal(eps, TYPES['C']) or c == scal(eps, TYPES['E'])) else 'opp')
                if key not in per_dev_worst or r < per_dev_worst[key][0]:
                    per_dev_worst[key] = (r, pp, qq, b, J)
                if worstA is None or r < worstA[0]:
                    worstA = (r, pp, qq, b, J, c)
log(f"(A) FD1 at true values: {nA} (b,J,c,p,q) cases, all s_J > 2 delta_p rho.  Global min ratio {float(worstA[0]):.6f} "
    f"at p={worstA[1]} q={worstA[2]} b={worstA[3]} J={worstA[4]} c={worstA[5]}")
for k in sorted(per_dev_worst):
    r, pp, qq, b, J = per_dev_worst[k]
    log(f"    {k:6s}: min ratio {float(r):.6f} (p={pp}, q={qq}, b={b}, J={J})")

# (B) + (C)
worstB = None; worstC = None; nB = nC = 0; worst_k3 = None
for (pp, qq) in pairs:
    p = Fr(pp); q = Fr(qq); P = p - 1; Q = q - 1
    M = T(2, p); Dp = d_def(2, p)
    Bt = TYPES['B']
    for b in bs:
        mu = pot(b + 2, q); rho = mu[b - 1]; need = 4 * P * rho
        zeta_bm1 = tuple(Fr(v) for v in Bt)
        for c in ALLC:
            s = s_at(M, Q, mu[b - 2], c, zeta_bm1, Dp)
            is_chain = (c == neg(Bt))
            if is_chain and P == 2:
                continue
            nB += 1
            assert s > need, ("FD2(a) FAILS", pp, qq, b, c, s / need)
            if worstB is None or s / need < worstB[0]:
                worstB = (s / need, pp, qq, b, c)
        if P != 2:
            continue
        # (C) P = 2: walk down the B-chain
        chain = Fr(0)
        zeta = zeta_bm1
        for Jp in range(b - 1, -2, -1):
            if Jp == -1:
                # full chain: kappa from (M zeta_{-1})_2
                kappa = 2 * max(Fr(0), -matvec(M, zeta)[2])
                tot = chain + kappa
                nC += 1
                assert tot > 8 * rho, ("FD2(b) full chain FAILS", pp, qq, b)
                if worstC is None or tot / (8 * rho) < worstC[0]:
                    worstC = (tot / (8 * rho), pp, qq, b, 'full chain')
                break
            # state at Jp is zeta (= zeta_{Jp}); chain column there would be (-1)^Jp B
            if Jp <= b - 2:   # deviation possible at Jp (c_{b-1} is chain by assumption of (b))
                for c in ALLC:
                    if c == scal((-1) ** Jp, Bt):
                        continue
                    sJ = s_at(M, Q, mu[Jp - 1], c, zeta, Dp)
                    tot = chain + sJ
                    nC += 1
                    assert tot > 8 * rho, ("FD2(b) FAILS", pp, qq, b, Jp, c)
                    if worstC is None or tot / (8 * rho) < worstC[0]:
                        worstC = (tot / (8 * rho), pp, qq, b, (Jp, c))
            c = scal((-1) ** Jp, Bt)
            sc = s_at(M, Q, mu[Jp - 1], c, zeta, Dp)
            assert sc == Q * (1 + mu[Jp - 1]) / q * 2 * (P - 1) ** 2
            chain += sc
            if Jp == b - 3:   # chain now covers b-1, b-2, b-3: the k >= 3 claim
                assert chain > 8 * rho, ("k>=3 chain alone fails", pp, qq, b)
                if worst_k3 is None or chain / (8 * rho) < worst_k3[0]:
                    worst_k3 = (chain / (8 * rho), pp, qq, b)
            zeta = tuple((zeta[k] + Q * c[k]) / q for k in range(3))
log(f"(B) FD2(a): {nB} cases, all s_(b-1) > 4P rho; min ratio {float(worstB[0]):.6f} at p={worstB[1]} q={worstB[2]} b={worstB[3]} c={worstB[4]}")
log(f"(C) FD2(b) (P=2): {nC} cases, all chain + s_J' (+kappa) > 8 rho; min ratio {float(worstC[0]):.6f} at p={worstC[1]} q={worstC[2]} "
    f"b={worstC[3]} {worstC[4]}")
log(f"    k>=3 claim (chain cost of b-1,b-2,b-3 alone > 8 rho): min ratio {float(worst_k3[0]):.6f} at p={worst_k3[1]} q={worst_k3[2]} b={worst_k3[3]}")

# (D) dense grid over the relaxed boxes (uses the verified closed forms from rv_fd_forms: s_derived)
from rv_fd_forms import s_derived  # noqa: E402  (derived, and verified == direct definition)
grid_n = 24
nD = 0; worstD = None
PQs = [(Fr(4), Fr(2)), (Fr(4), Fr(3)), (Fr(9, 2), Fr(5, 2)), (Fr(10), Fr(2)), (Fr(100), Fr(2)), (Fr(1000), Fr(2)), (Fr(6), Fr(20)),
       (Fr(2), Fr(4)), (Fr(2), Fr(6)), (Fr(2), Fr(100)), (Fr(2), Fr(1000))]
for (P, Q) in PQs:
    q = Q + 1; dp = P * P + 1
    mu0 = (Q - 1) / q; mu1 = (Q * Q + 1) / q ** 2; L = Q / (q + 1)
    lin = lambda a, b_: [a + (b_ - a) * Fr(k, grid_n) for k in range(grid_n + 1)]
    boxes = {
        'R0': ([Fr(1)], lin(mu0, L), lambda MU, m: 2 * dp * (Q - m) / q),
        'R1': (lin(mu0, L), [Fr(1)], lambda MU, m: 2 * dp * (Q - MU) / q),
        'R2a': (lin(L, mu1), lin(mu0, L), lambda MU, m: 2 * dp * MU),
        'R2b': (lin(mu0, L), lin(L, mu1), lambda MU, m: 2 * dp * m),
    }
    for dev in ['Asame', 'Bsame', 'Bopp', 'Csame', 'Copp', 'Esame', 'Eopp']:
        for name, (MUs, ms, need) in boxes.items():
            vals = {}
            for MU in MUs:
                for m in ms:
                    vals[(MU, m)] = s_derived('fd1', dev, P, Q, MU, m) - need(MU, m)
            gmin = min(vals.values())
            vmin = min(vals[(a, c)] for a in (MUs[0], MUs[-1]) for c in (ms[0], ms[-1]))
            assert gmin > 0, ("relaxed FD1 not positive", P, Q, dev, name, gmin)
            assert gmin >= vmin, ("grid min below vertex min (concavity?)", P, Q, dev, name)
            nD += len(vals)
    # FD2 (a) and (b)
    for dev in ['Asame', 'Aopp', 'Bsame', 'Csame', 'Copp', 'Esame', 'Eopp', 'chain']:
        if dev == 'chain' and P == 2:
            continue
        vals = [s_derived('chain', dev, P, Q, MU, Fr(1)) - 4 * P * (Q - MU) / q for MU in lin(mu0, L)]
        assert min(vals) > 0 and min(vals) >= min(vals[0], vals[-1]); nD += len(vals)
        if P == 2 and dev != 'chain':
            v1 = []
            for MU in lin(L, Fr(1)):
                x = (Q - MU) / q; rho = (Q - x) / q
                v1.append(2 * (P - 1) ** 2 * Q * (1 + x) / q + s_derived('chain', dev, P, Q, MU, mu0) - 4 * P * rho)
            assert min(v1) > 0 and min(v1) >= min(v1[0], v1[-1]); nD += len(v1)
            v2 = []
            for MU in lin(mu0, L):
                y = (Q - MU) / q; x = (Q - y) / q; rho = (Q - x) / q
                v2.append(2 * (P - 1) ** 2 * Q * (2 + x + y) / q + s_derived('chain', dev, P, Q, MU, mu1) - 4 * P * rho)
            assert min(v2) > 0 and min(v2) >= min(v2[0], v2[-1]); nD += len(v2)
log(f"(D) dense exact grid over relaxed boxes ({len(PQs)} (P,Q) incl. P=4,Q=2 and P=2,Q=4): {nD} points, all positive, "
    f"grid min >= vertex min everywhere")

# the text's k>=3 inequality at true values: 2(chat_{b-1}+chat_{b-2}+chat_{b-3}) - 8 rho  vs  (2/q)[(4Q+8)mu0 - 2Q + 2QL]
viol = []
for qq in (5, 7, 11, 101, Fr(9, 2)):
    q = Fr(qq); Q = q - 1; mu = pot(50, q); L = Q / (q + 1)
    for b in range(4, 41, 2):
        lhs = 2 * Q * (3 + mu[b - 2] + mu[b - 3] + mu[b - 4]) / q - 8 * (Q - mu[b - 2]) / q
        rhs = (2 / q) * ((4 * Q + 8) * mu[0] - 2 * Q + 2 * Q * L)
        if lhs < rhs:
            viol.append((qq, b, float(lhs), float(rhs)))
log(f"text's k>=3 inequality '... >= (2/q)[(4Q+8)mu0-2Q+2QL]' at true values: violated in {len(viol)} of 95 (q,b) cases"
    + (f", e.g. {viol[0]}" if viol else ""))
log("DONE")
