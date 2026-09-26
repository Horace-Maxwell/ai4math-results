"""Test a signed potential for the 1D two-vector problem (exponent pairs (1,m),(m,1), m odd).

Path side: x (exponent m), F-side: T_1(r) with R = r-1, g_R(U,V) = R|U-V| + |RU+V|.
Candidate potential  Pi_j(U,V) = mu_j g_R(U,V) - 2 lam_j (eps_j (RU+V))^-,
   lam_j = rho/mu_{m-2-j}, eps_j = (-1)^{j+1}, rho = mu_{m-1}.
Step j (0<=j<=m-1), inputs (u_j,v_j) in {+-1}^2, state (U,V)=(U_j,V_j):
   g_R(a,b) + Pi_{j-1}(U',V') - Pi_j(U,V) <= c_j (3R-1),  a=(P/x)(u_j-U), U'=(U+P u_j)/x.
Final: Pi_{m-1}(u_m,-1) <= mu_{m-1}(3R-1) - 2(R-1)rho.   Initial: Pi_{-1} = g_R - 2(RU+V)^- (by construction).
We test (a) all reachable states (exhaustive over sign vectors), (b) a grid on the box of magnitudes.
"""
import itertools, sys
from fractions import Fraction as Fr
import numpy as np


def setup(x, m):
    x = float(x); P = x - 1
    mu = {-1: 1.0}
    for k in range(m):
        mu[k] = (P - mu[k - 1]) / x
    return x, P, mu


def gR(R, U, V):
    return R * abs(U - V) + abs(R * U + V)


def run(x, R, m, grid=41, verbose=False):
    x, P, mu = setup(x, m)
    rho = mu[m - 1]
    lam = {j: rho / mu[m - 2 - j] for j in range(-1, m)}
    c = {j: P * (1 + mu[j - 1]) / x for j in range(m)}

    def Pi(j, U, V):
        eps = (-1) ** (j + 1)
        return mu[j] * gR(R, U, V) - 2 * lam[j] * max(0.0, -(eps * (R * U + V)))

    worst = -1e9; wh = None
    # (a) reachable states: U_j = z_j(u) for all sign vectors on positions j+1..m
    for j in range(m):
        states = set()
        for tail in itertools.product([1, -1], repeat=m - j):  # entries j+1..m
            z = tail[-1] * 1.0
            for t in range(len(tail) - 2, -1, -1):
                z = (z + P * tail[t]) / x
            states.add(round(z, 12))
        states = sorted(states)
        for U in states:
            for V in states:
                for uj in (1, -1):
                    for vj in (1, -1):
                        a = (P / x) * (uj - U); b = (P / x) * (vj - V)
                        Up = (U + P * uj) / x; Vp = (V + P * vj) / x
                        s = gR(R, a, b) + Pi(j - 1, Up, Vp) - Pi(j, U, V) - c[j] * (3 * R - 1)
                        if s > worst:
                            worst = s; wh = ('reach', j, U, V, uj, vj)
    # final
    fin = max(Pi(m - 1, um, -1.0) - (mu[m - 1] * (3 * R - 1) - 2 * (R - 1) * rho) for um in (1.0, -1.0))
    # (b) box grid
    worst_box = -1e9; whb = None
    mags = np.linspace((x - 2) / x, 1.0, grid)
    for j in range(m):
        for su in (1, -1):
            for sv in (1, -1):
                for mu_ in mags:
                    for mv in mags:
                        U = su * mu_; V = sv * mv
                        for uj in (1, -1):
                            for vj in (1, -1):
                                a = (P / x) * (uj - U); b = (P / x) * (vj - V)
                                Up = (U + P * uj) / x; Vp = (V + P * vj) / x
                                s = gR(R, a, b) + Pi(j - 1, Up, Vp) - Pi(j, U, V) - c[j] * (3 * R - 1)
                                if s > worst_box:
                                    worst_box = s; whb = ('box', j, U, V, uj, vj)
    return worst, wh, fin, worst_box, whb


if __name__ == "__main__":
    for m in [1, 3, 5, 7]:
        for x in [3, 5, 7, 4, 11]:
            for R in [2, 4, 6, 10, 40]:
                if x == 3 and R < 4:
                    continue
                w, wh, fin, wb, whb = run(x, R, m)
                print(f"m={m} x={x} R={R}: max step excess reachable={w:+.3e} final={fin:+.3e} box={wb:+.3e}  at {wh if w>1e-12 else ''} {whb if wb>1e-12 else ''}")
        sys.stdout.flush()
