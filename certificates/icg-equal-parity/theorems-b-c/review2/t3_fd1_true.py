"""Referee-2, test 3.  FD1_a at the TRUE parameter values (no vertex reduction), and regime bookkeeping.

For a in {3, 4}, every b of the parity of a with b <= BMAX, every J in 0..b-1:
 (i)  regime mapping as in PROOF.md sec. 11 / generic_prover.regimes_FD1: check that (mu_{J-1}, mu_{b-2-J}) lies in the box
      of the regime the index pair is mapped to, and that rho = mu_{b-1} equals the exact expression (R0/R1/B1) or is <= the
      substituted upper bound (R2a/R2b/R2odd/R2even).  (Also checks that EVERY J is mapped to exactly one regime.)
 (ii) s_J(c, zeta_J) - 2 delta_a rho > 0 for every deviation c != -eps s_a, computed from the cell DEFINITION at the exact
      state zeta_J = eps mu_{b-2-J} s_a; min ratio s_J / (2 delta_a rho) reported.
Parameters: integer and non-integer points of both regions, incl. the corners (P,Q) = (4,2), (2,4) and large values.
"""
import itertools, sys
from fractions import Fraction as Fr
from r2core import T, mus, matvec, l1, svec, dd, de, surplus_direct

BMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 31
out = open('logs/t3_fd1_true.log', 'w')
def log(*a):
    s = ' '.join(str(x) for x in a); print(s); out.write(s + '\n'); out.flush()

def regime(a, b, J):
    if a % 2 == 0:
        if J == 0: return 'R0'
        if J == b - 1: return 'R1'
        return 'R2a' if (J - 1) % 2 == 1 else 'R2b'
    if b == 1: return 'B1'
    if J == 0: return 'R0'
    if J == b - 1: return 'R1'
    return 'R2odd' if (J - 1) % 2 == 1 else 'R2even'

def check_box(reg, mu, J, b, q):
    Q = q - 1
    mu0 = (Q - 1) / q; mu1 = (Q ** 2 + 1) / q ** 2; L = Q / (q + 1)
    MU = mu[J - 1]; m = mu[b - 2 - J]; rho = mu[b - 1]
    inr = lambda x, lo, hi: lo <= x <= hi
    if reg == 'R0':
        ok = MU == 1 and ((a_even and inr(m, mu0, L)) or (not a_even and inr(m, L, mu1))) and rho == (Q - m) / q
    elif reg == 'R1':
        ok = m == 1 and ((a_even and inr(MU, mu0, L)) or (not a_even and inr(MU, L, mu1))) and rho == (Q - MU) / q
    elif reg == 'R2a':
        ok = inr(MU, L, mu1) and inr(m, mu0, L) and rho <= MU
    elif reg == 'R2b':
        ok = inr(MU, mu0, L) and inr(m, L, mu1) and rho <= m
    elif reg == 'B1':
        ok = MU == 1 and m == 1 and rho == mu0
    elif reg == 'R2odd':
        ok = inr(MU, L, mu1) and inr(m, L, mu1) and rho <= L
    elif reg == 'R2even':
        ok = inr(MU, mu0, L) and inr(m, mu0, L) and rho <= L
    return ok

params = [(Fr(5), Fr(3)), (Fr(7), Fr(3)), (Fr(11), Fr(3)), (Fr(101), Fr(3)), (Fr(3), Fr(5)), (Fr(3), Fr(7)), (Fr(3), Fr(101)),
          (Fr(5), Fr(7)), (Fr(7), Fr(5)), (Fr(11, 2), Fr(7, 2)), (Fr(21, 4), Fr(3)), (Fr(5), Fr(13, 4)), (Fr(3), Fr(21, 4)),
          (Fr(1001), Fr(1001)), (Fr(5), Fr(1001)), (Fr(3), Fr(1001))]
for a in (3, 4):
    a_even = (a % 2 == 0)
    sa = svec(a)
    vecs = list(itertools.product([1, -1], repeat=a + 1))
    for (p, q) in params:
        Q = q - 1
        M = T(a, p); Da = dd(a, p); da = de(a, p)
        worst = None; nreg = {}
        for b in [bb for bb in range(1, BMAX + 1) if (a + bb) % 2 == 0]:
            mu = mus(b + 2, q); rho = mu[b - 1]; need = 2 * da * rho
            for J in range(b):
                reg = regime(a, b, J)
                nreg[reg] = nreg.get(reg, 0) + 1
                assert check_box(reg, mu, J, b, q), ("regime box violated", a, b, J, reg, p, q)
                eps = (-1) ** J; m = mu[b - 2 - J]
                zeta = [eps * m * x for x in sa]
                cont = [-eps * x for x in sa]
                for c in vecs:
                    if list(c) == cont: continue
                    sJ = surplus_direct(M, Da, Q, q, mu[J - 1], list(c), zeta)
                    r = sJ / need
                    assert r > 1, ("FD1 fails", a, b, J, c, p, q, float(r))
                    if worst is None or r < worst[0]: worst = (r, b, J, c)
        log(f"a={a} p={p} q={q}: b<= {BMAX}, all J: regimes {nreg} boxes OK; FD1 true min s_J/(2 delta_a rho) = "
            f"{float(worst[0]):.5f} at b={worst[1]} J={worst[2]} dev={worst[3]}")
