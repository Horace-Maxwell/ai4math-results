"""Items 5-6 (closed forms).  Referee's own cell-by-cell derivation (from the four case values of h, NOT from the table):

h_mu(A,B), A >= 0:  0<=B<=A: -2(Q-mu)B;  B>A: 2(mu B - Q A);  -QA<=B<0: 0;  B<-QA: 2 mu(|B|-QA);  h(0,B)=2mu|B|;  h(-A,-B)=h(A,B).

FD1: state vector B = eps*m*beta, beta = alpha(A) = (2pP, -2P^2, P^2+1); column c = sigma*eps*t ("same": sigma=+1).
By h(-A,-B)=h(A,B) it suffices to take eps=+1.  Per coordinate i (value of h_i):
  A same : -4(Q-mu)pPm | -4(Q-mu)P^2 m                                  | -2(Q-mu)(P^2+1)m
  B same : 0 [A=-2pP,B=+2pPm: -QA<=B<0 after flip] | Pm<=1: -4(Q-mu)P^2m, else 4P(mu Pm - Q) | -2(Q-mu)(P^2+1)m
  B opp  : -4(Q-mu)pPm | Pm<=Q: 0, else 4 mu P(Pm-Q)                    | 0
  C same : 4 mu pPm    | -4(Q-mu)P^2 m    | m(P^2+1)<=P^2-1: -2(Q-mu)(P^2+1)m, else 2(mu m(P^2+1) - Q(P^2-1))
  C opp  : 4 mu pPm    | 0                | 0
  E same : 4 mu pPm    | 4 mu P^2 m       | -2(Q-mu)(P^2+1)m
  E opp  : 4 mu pPm    | 4 mu P^2 m       | 0
B-chain: state eps'*m*gamma, gamma = alpha(B) = (-2pP, -2P, p^2-2):
  chain -B: 0 | 0 | 0
  A same : 0 | -4(Q-mu)Pm | m(p^2-2)<=P^2+1: -2(Q-mu)m(p^2-2), else 2(mu m(p^2-2) - Q(P^2+1))
  A opp  : -4(Q-mu)pPm | 0 | 0
  B same : -4(Q-mu)pPm | -4(Q-mu)Pm | -2(Q-mu)m(p^2-2)
  C same : 4 mu pPm | -4(Q-mu)Pm | m(p^2-2)<=P^2-1: -2(Q-mu)m(p^2-2), else 2(mu m(p^2-2) - Q(P^2-1))
  C opp  : 4 mu pPm | 0 | 0
  E same : 4 mu pPm | 4 mu Pm | -2(Q-mu)m(p^2-2)
  E opp  : 4 mu pPm | 4 mu Pm | 0
and s = Q(1+mu)/q * Delta(t) - (h_0+h_1+h_2)/q.

Checks:
 (1) derived per-cell values == direct cell definition, eps = +-1, at random exact points of both regions and at all
     switching points (Pm = 1, Pm = Q, m(P^2+1) = P^2-1, m(p^2-2) = P^2+1, m(p^2-2) = P^2-1, m in {0,1}, mu in {0,1}).
 (2) PROOF.md tables (transcribed verbatim below) == derived, at the same points.
 (3) symbolic: each case split coincides with the min{...} of the table (difference of the two min-arguments is Q*(switching
     quantity)); the non-split cells' side conditions hold on the regions (coefficient certificates).
 (4) completeness: the 7 FD1 deviations + the anti column = {+-1}^3; the 7 chain deviations + chain column = {+-1}^3.
"""
import itertools, random, sys
from fractions import Fraction as Fr
import sympy as sp
from rv_common import T, matvec, l1, hcell, d_def, TYPES, S2, scal

random.seed(99)
out = []
def log(s):
    print(s); sys.stdout.flush(); out.append(s)

DEVS = {'Asame': ('A', 1), 'Bsame': ('B', 1), 'Bopp': ('B', -1), 'Csame': ('C', 1), 'Copp': ('C', -1),
        'Esame': ('E', 1), 'Eopp': ('E', -1)}
CDEVS = {'chain': ('B', -1), 'Asame': ('A', 1), 'Aopp': ('A', -1), 'Bsame': ('B', 1), 'Csame': ('C', 1),
         'Copp': ('C', -1), 'Esame': ('E', 1), 'Eopp': ('E', -1)}


def Delta_t(t, P):
    return {'A': 0, 'B': 2 * (P - 1) ** 2, 'C': 2 * (P * P + 1), 'E': 4 * P * P}[t]


def cells_fd1(dev, P, Q, mu, m):
    p = P + 1
    if dev == 'Asame': return [-4 * (Q - mu) * p * P * m, -4 * (Q - mu) * P * P * m, -2 * (Q - mu) * (P * P + 1) * m]
    if dev == 'Bsame':
        h1 = -4 * (Q - mu) * P * P * m if P * m <= 1 else 4 * P * (mu * P * m - Q)
        return [0, h1, -2 * (Q - mu) * (P * P + 1) * m]
    if dev == 'Bopp':
        h1 = 0 if P * m <= Q else 4 * mu * P * (P * m - Q)
        return [-4 * (Q - mu) * p * P * m, h1, 0]
    if dev == 'Csame':
        h2 = -2 * (Q - mu) * (P * P + 1) * m if m * (P * P + 1) <= P * P - 1 else 2 * (mu * m * (P * P + 1) - Q * (P * P - 1))
        return [4 * mu * p * P * m, -4 * (Q - mu) * P * P * m, h2]
    if dev == 'Copp': return [4 * mu * p * P * m, 0, 0]
    if dev == 'Esame': return [4 * mu * p * P * m, 4 * mu * P * P * m, -2 * (Q - mu) * (P * P + 1) * m]
    if dev == 'Eopp': return [4 * mu * p * P * m, 4 * mu * P * P * m, 0]


def cells_chain(dev, P, Q, mu, m):
    p = P + 1; g2 = p * p - 2
    if dev == 'chain': return [0, 0, 0]
    if dev == 'Asame':
        h2 = -2 * (Q - mu) * m * g2 if m * g2 <= P * P + 1 else 2 * (mu * m * g2 - Q * (P * P + 1))
        return [0, -4 * (Q - mu) * P * m, h2]
    if dev == 'Aopp': return [-4 * (Q - mu) * p * P * m, 0, 0]
    if dev == 'Bsame': return [-4 * (Q - mu) * p * P * m, -4 * (Q - mu) * P * m, -2 * (Q - mu) * m * g2]
    if dev == 'Csame':
        h2 = -2 * (Q - mu) * m * g2 if m * g2 <= P * P - 1 else 2 * (mu * m * g2 - Q * (P * P - 1))
        return [4 * mu * p * P * m, -4 * (Q - mu) * P * m, h2]
    if dev == 'Copp': return [4 * mu * p * P * m, 0, 0]
    if dev == 'Esame': return [4 * mu * p * P * m, 4 * mu * P * m, -2 * (Q - mu) * m * g2]
    if dev == 'Eopp': return [4 * mu * p * P * m, 4 * mu * P * m, 0]


def s_derived(kind, dev, P, Q, mu, m):
    q = Q + 1
    t = (DEVS if kind == 'fd1' else CDEVS)[dev][0]
    cells = (cells_fd1 if kind == 'fd1' else cells_chain)(dev, P, Q, mu, m)
    return Q * (1 + mu) / q * Delta_t(t, P) - sum(cells) / q


def s_direct(kind, dev, P, Q, mu, m, eps):
    """from the definition: column c = sigma*eps*t, state zeta = eps*m*(ref type) in {+-1}^3 coordinates."""
    p = P + 1; q = Q + 1
    M = T(2, p)
    t, sigma = (DEVS if kind == 'fd1' else CDEVS)[dev]
    ref = TYPES['A'] if kind == 'fd1' else TYPES['B']
    c = scal(sigma * eps, TYPES[t])
    A = matvec(M, c); B = matvec(M, scal(eps * m, ref))
    Delta = d_def(2, p) - l1(A)
    return Q * (1 + mu) / q * Delta - sum(hcell(Q, mu, A[i], B[i]) for i in range(3)) / q, [hcell(Q, mu, A[i], B[i]) for i in range(3)]


# ----- PROOF.md tables, transcribed verbatim (lines 105-113 and 149-158) -----
def s_claimed(kind, dev, P, Q, mu, m):
    p = P + 1; q = Q + 1
    ch = Q * (1 + mu) / q; muJ = (Q - mu) / q; Dp = 5 * P * P + 2 * P + 1
    pos = lambda x: x if x > 0 else 0
    if kind == 'fd1':
        return {
            'Asame': lambda: 2 * muJ * m * Dp,
            'Bsame': lambda: 2 * (P - 1) ** 2 * ch + 2 * muJ * (P * P + 1) * m + (4 * P / q) * min((Q - mu) * P * m, Q - mu * P * m),
            'Bopp': lambda: 2 * (P - 1) ** 2 * ch + 4 * muJ * p * P * m - (4 * mu * P / q) * pos(P * m - Q),
            'Csame': lambda: 2 * (P * P + 1) * ch - (4 * mu / q) * p * P * m + 4 * muJ * P * P * m
                            + (2 / q) * min((Q - mu) * (P * P + 1) * m, Q * (P * P - 1) - mu * (P * P + 1) * m),
            'Copp': lambda: 2 * (P * P + 1) * ch - (4 * mu / q) * p * P * m,
            'Esame': lambda: 4 * P * P * ch - (4 * mu / q) * (p * P + P * P) * m + 2 * muJ * (P * P + 1) * m,
            'Eopp': lambda: 4 * P * P * ch - (4 * mu / q) * (p * P + P * P) * m,
        }[dev]()
    return {
        'chain': lambda: 2 * (P - 1) ** 2 * ch,
        'Asame': lambda: 4 * muJ * P * m + (2 / q) * min((Q - mu) * (p * p - 2) * m, Q * (P * P + 1) - mu * (p * p - 2) * m),
        'Aopp': lambda: 4 * muJ * p * P * m,
        'Bsame': lambda: 2 * (P - 1) ** 2 * ch + 2 * muJ * m * (3 * p * p - 4),
        'Csame': lambda: 2 * (P * P + 1) * ch - (4 * mu / q) * p * P * m + 4 * muJ * P * m
                        + (2 / q) * min((Q - mu) * (p * p - 2) * m, Q * (P * P - 1) - mu * (p * p - 2) * m),
        'Copp': lambda: 2 * (P * P + 1) * ch - (4 * mu / q) * p * P * m,
        'Esame': lambda: 4 * P * P * ch - (4 * mu / q) * (p * P + P) * m + 2 * muJ * (p * p - 2) * m,
        'Eopp': lambda: 4 * P * P * ch - (4 * mu / q) * (p * P + P) * m,
    }[dev]()


def sample_points():
    pts = []
    for trial in range(2500):
        if trial % 2 == 0:
            P = Fr(4) + Fr(random.randint(0, 400), random.randint(1, 10)); Q = Fr(2) + Fr(random.randint(0, 400), random.randint(1, 10))
        else:
            P = Fr(2); Q = Fr(4) + Fr(random.randint(0, 400), random.randint(1, 10))
        mu = Fr(random.randint(0, 997), 997); m = Fr(random.randint(0, 991), 991)
        pts.append((P, Q, mu, m))
    # switching points and endpoints
    for P in (Fr(4), Fr(9, 2), Fr(7), Fr(2)):
        for Q in ((Fr(2), Fr(5, 2), Fr(9)) if P != 2 else (Fr(4), Fr(9, 2), Fr(9))):
            p = P + 1
            ms = {Fr(0), Fr(1), 1 / P, min(Fr(1), Q / P), (P * P - 1) / (P * P + 1),
                  min(Fr(1), (P * P + 1) / (p * p - 2)), (P * P - 1) / (p * p - 2)}
            for m in list(ms):
                for dm in (Fr(0), Fr(1, 10 ** 6), -Fr(1, 10 ** 6)):
                    mm = m + dm
                    if 0 <= mm <= 1:
                        for mu in (Fr(0), Fr(1), Fr(1, 3), Fr(3, 5)):
                            pts.append((P, Q, mu, mm))
    return pts


if __name__ == '__main__':
    pts = sample_points()
    n1 = n2 = 0
    for (P, Q, mu, m) in pts:
        for kind, D in (('fd1', DEVS), ('chain', CDEVS)):
            for dev in D:
                der = s_derived(kind, dev, P, Q, mu, m)
                cells_der = (cells_fd1 if kind == 'fd1' else cells_chain)(dev, P, Q, mu, m)
                for eps in (1, -1):
                    d, cells_dir = s_direct(kind, dev, P, Q, mu, m, eps)
                    assert cells_dir == cells_der, (kind, dev, P, Q, mu, m, eps, cells_dir, cells_der)
                    assert d == der
                    n1 += 1
                assert s_claimed(kind, dev, P, Q, mu, m) == der, (kind, dev, P, Q, mu, m)
                n2 += 1
    log(f"(1) referee's per-cell derivation == direct cell definition (eps=+-1): {n1} exact checks "
        f"({len(pts)} parameter points incl. all switching points +-1e-6, both regions)")
    log(f"(2) PROOF.md tables (FD1: 7 forms, FD2: 8 forms) == derivation: {n2} exact checks, 0 mismatches")

    # (3) symbolic: min-structure and side conditions
    P, Q, mu, m, s, t = sp.symbols('P Q mu m s t', nonnegative=True)
    p = P + 1
    splits = [
        ('FD1 Bsame h1', (Q - mu) * P * m - (Q - mu * P * m), Q * (P * m - 1)),
        ('FD1 Csame h2', (Q - mu) * (P ** 2 + 1) * m - (Q * (P ** 2 - 1) - mu * (P ** 2 + 1) * m), Q * (m * (P ** 2 + 1) - (P ** 2 - 1))),
        ('chain Asame h2', (Q - mu) * (p ** 2 - 2) * m - (Q * (P ** 2 + 1) - mu * (p ** 2 - 2) * m), Q * (m * (p ** 2 - 2) - (P ** 2 + 1))),
        ('chain Csame h2', (Q - mu) * (p ** 2 - 2) * m - (Q * (P ** 2 - 1) - mu * (p ** 2 - 2) * m), Q * (m * (p ** 2 - 2) - (P ** 2 - 1))),
    ]
    for name, diff, expect in splits:
        assert sp.expand(diff - expect) == 0, name
        log(f"(3) {name}: (first min-arg) - (second) = {sp.factor(expect)}  => min picks the case branch of the cell: OK")
    # side conditions used for the non-split cells (must hold for all m in [0,1], P>=2 and Q>=2 (big: P>=4,Q>=2; p3: P=2,Q>=4))
    side = {
        'm <= Q (FD1 B same i=0, B opp i=0 as 0<=B<=A...)': Q - 1,
        'm(P^2+1) <= p^2-2 (FD1 B same i=2)': (p ** 2 - 2) - (P ** 2 + 1),
        'm(P^2+1) <= Q(p^2-2) (FD1 B opp i=2)': Q * (p ** 2 - 2) - (P ** 2 + 1),
        'm 2P^2 <= 2pP (FD1 C same i=1)': 2 * p * P - 2 * P ** 2,
        'm(P^2+1) <= Q(P^2-1) (FD1 C opp i=2)': Q * (P ** 2 - 1) - (P ** 2 + 1),
        'm(P^2+1) <= p^2 (FD1 E same i=2)': p ** 2 - (P ** 2 + 1),
        'm 2Pm <= 2QP^2 (chain A opp i=1)': 2 * Q * P ** 2 - 2 * P,
        'm(p^2-2) <= Q(P^2+1) (chain A opp i=2)': Q * (P ** 2 + 1) - (p ** 2 - 2),
        'm(p^2-2) <= Q(P^2-1) (chain C opp i=2)': Q * (P ** 2 - 1) - (p ** 2 - 2),
        'm 2P <= 2pP (chain C same i=1)': 2 * p * P - 2 * P,
        'm(p^2-2) <= p^2 (chain E same i=2)': Fr(2),
        'm 2P^2 m <= Q 2P^2 (FD1 A same/B opp i=1 region)': 2 * Q * P ** 2 - 2 * P ** 2,
    }
    for name, e in side.items():
        for reg in ('big', 'p3'):
            ee = sp.expand(sp.sympify(e).subs({P: 4 + s, Q: 2 + t}, simultaneous=True) if reg == 'big'
                           else sp.sympify(e).subs({P: 2, Q: 4 + t}, simultaneous=True))
            pe = sp.Poly(ee, s, t)
            ok = all(c >= 0 for c in pe.coeffs())
            assert ok, (name, reg, ee)
    log(f"(3) {len(side)} side conditions of the unsplit cells hold on both regions for all m in [0,1] (coefficient check): OK")

    # (4) completeness
    allc = set(itertools.product((1, -1), repeat=3))
    for eps in (1, -1):
        got = {scal(sig * eps, TYPES[t]) for (t, sig) in DEVS.values()}
        assert len(got) == 7 and got | {scal(-eps, S2)} == allc and scal(-eps, S2) not in got
        got = {scal(sig * eps, TYPES[t]) for (t, sig) in CDEVS.values()}
        assert len(got) == 8 and got == allc
    log("(4) completeness: FD1 7 deviations + anti column (-eps s_2) = {+-1}^3; chain table 8 columns = {+-1}^3: OK")
    log("DONE")
