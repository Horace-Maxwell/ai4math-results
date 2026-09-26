"""1D two-vector reduction for exponent pairs (1,m) / (m,1), m odd.

For a = 1: Z = T_1(p) Y T_b(q)^T has rows -(p-1) N(y0-y1) and N((p-1) y0 + y1), N = T_b(q).
Hence with R = p-1, x = q, m = b, u = y0, v = y1 (v_m = -1):
   G(Y)/x^m = R*Nrm(u-v) + Nrm(R u + v) - 2*(z_{-1}(R u + v))^-,   Nrm(w) = ||T_m(x) w||_1 / x^m,
and the conjecture is  G <= (3R-1) Dhat_m(x) - 2(R-1) rho_m(x).
(b = 1 is the same statement with the roles of the primes exchanged.)
This script (1) checks the reduction against the full matrix model exactly, (2) scans the 1D inequality
exhaustively (float64) for real x>=3, R>=2 and odd m, and reports the margin.
"""
import numpy as np, itertools, sys
from fractions import Fraction as Fr
from core import T, Gval, dfun, delta_last, path


def Lmat(m, x):
    """matrix of w -> (z_{-1}, z_{-1}-z_0, ..., z_{m-2}-z_{m-1}) (float)."""
    M = np.zeros((m + 1, m + 1))
    for i in range(m + 1):
        e = [0] * (m + 1); e[i] = 1
        z = path(e, x)
        col = [z[-1]] + [z[k - 1] - z[k] for k in range(m)]
        M[:, i] = [float(c) for c in col]
    return M


def check_reduction():
    for (m, p, q) in [(1, 5, 3), (3, 5, 3), (3, 3, 5), (5, 7, 3), (3, 11, 13)]:
        N = T(m, q)
        for bits in itertools.product([1, -1], repeat=2 * (m + 1)):
            u = list(bits[:m + 1]); v = list(bits[m + 1:])
            if v[m] != -1:
                continue
            Y = [u, v]
            g = Gval(Y, p, q)
            R = p - 1
            def nrm(w):
                return sum(abs(sum(N[i][j] * w[j] for j in range(m + 1))) for i in range(m + 1))
            w2 = [R * u[j] + v[j] for j in range(m + 1)]
            zz = path(w2, q)[-1]
            g2 = R * nrm([u[j] - v[j] for j in range(m + 1)]) + nrm(w2) - 2 * max(0, -zz) * Fr(q) ** m
            assert g == g2, (m, p, q, u, v, g, g2)
    print("reduction a=1 verified exactly on sample shapes")


def scan(m, x, R):
    L = Lmat(m, x)
    Dh = float(dfun(m, x)) / float(x) ** m
    rho = float(delta_last(m, x)) / float(x) ** m
    tgt = (3 * R - 1) * Dh - 2 * (R - 1) * rho
    n = m + 1
    idx = np.arange(1 << n)
    S = ((idx[:, None] >> np.arange(n)) & 1) * 2 - 1  # all sign vectors
    V = S[S[:, m] == -1]
    best = -1e300; arg = None; vals = []
    LU = S @ L.T
    LV = V @ L.T
    for iu in range(len(S)):
        d = np.abs(LU[iu][None, :] - LV).sum(1)  # Nrm(u-v)
        w = R * LU[iu][None, :] + LV
        g = R * d + np.abs(w).sum(1) - 2 * np.maximum(0, -w[:, 0])
        j = int(np.argmax(g))
        vals.append(g)
        if g[j] > best:
            best = g[j]; arg = (S[iu].copy(), V[j].copy())
    allv = np.sort(np.concatenate(vals))[::-1]
    second = allv[allv < best - 1e-9 * abs(best)]
    return tgt, best, arg, (tgt - second[0]) / tgt if len(second) else float('nan'), int((allv >= best - 1e-9 * abs(best)).sum())


if __name__ == "__main__":
    check_reduction()
    worst = 1e9
    for m in [1, 3, 5, 7, 9, 11]:
        for x in [3, 3.5, 4, 5, 7, 11, 50]:
            for R in [2, 2.5, 3, 4, 6, 10, 40, 200]:
                tgt, best, arg, gap, ties = scan(m, x, R)
                ok = best <= tgt * (1 + 1e-12) + 1e-9
                worst = min(worst, (tgt - best) / tgt)
                if (not ok) or m <= 3 or x == 3:
                    print(f"m={m} x={x} R={R}: max={best:.6f} target={tgt:.6f} {'OK' if ok else 'FAIL'} ties={ties} relgap_next={gap:.4g} "
                          f"u={''.join('+' if t > 0 else '-' for t in arg[0])} v={''.join('+' if t > 0 else '-' for t in arg[1])}")
        sys.stdout.flush()
    print("worst relative margin (target-max)/target over scan:", worst)
