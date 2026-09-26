"""Item 3: Lemma S, adversarially and EXACTLY.

s(c, zeta, mu) = Q(1+mu)/q * Delta(c) - (1/q) sum_i h_mu((Mc)_i, (M zeta)_i),  zeta in [-1,1]^3 (ALL states, not only reachable).

For fixed (P,Q,c), zeta -> s is continuous and piecewise affine; its pieces are cut out by the hyperplanes
(M zeta)_i = beta, beta in {A_i, 0, -Q A_i} (kinks of |A-B|, |B|, |B+QA|), and the cube facets zeta_k = +-1.  Hence the exact
minimum over the cube is attained at a vertex of this arrangement: we enumerate all triples of hyperplanes, solve exactly, keep
the points in the cube, and evaluate.  The vertex set does not depend on mu, and s is affine in mu, so the minimum over
mu in [0,1] is attained at mu in {0,1}.  This gives the exact min over (zeta, mu) in [-1,1]^3 x [0,1].

We report, per type, the exact minimum and compare with the lower bounds of the hand proof:
  B: (2/q)[Q(1+mu)(P-1)^2 - 2 mu P (p-Q)^+],  C: (4/q)[P^2+1-mu(P-1)],  E: (8P/q)(P-mu);  A: min must be exactly 0.
Also: the hand-proof inequalities themselves are checked symbolically (sympy) on the parameter regions.
Also (informative): the same exact minimisation OUTSIDE the stated range, to see which hypotheses are used.
"""
import itertools, sys
from fractions import Fraction as Fr
import sympy as sp
from rv_common import T, matvec, l1, hcell, d_def, TYPES

out = []
def log(s):
    print(s); sys.stdout.flush(); out.append(s)


def solve3(rows, rhs):
    """exact 3x3 solve; returns None if singular."""
    a = [list(map(Fr, r)) + [Fr(v)] for r, v in zip(rows, rhs)]
    n = 3
    for col in range(n):
        piv = next((r for r in range(col, n) if a[r][col] != 0), None)
        if piv is None:
            return None
        a[col], a[piv] = a[piv], a[col]
        for r in range(n):
            if r != col and a[r][col] != 0:
                f = a[r][col] / a[col][col]
                a[r] = [x - f * y for x, y in zip(a[r], a[col])]
    return [a[i][3] / a[i][i] for i in range(n)]


def exact_min(P, Q, c):
    p = P + 1; q = Q + 1
    M = T(2, p)
    A = matvec(M, c)
    Dp = d_def(2, p)
    Delta = Dp - l1(A)
    planes = []
    for k in range(3):
        e = [0, 0, 0]; e[k] = 1
        planes += [(tuple(e), Fr(1)), (tuple(e), Fr(-1))]
    for i in range(3):
        for beta in {A[i], Fr(0), -Q * A[i]}:
            planes.append((tuple(M[i]), beta))
    verts = set()
    for tri in itertools.combinations(planes, 3):
        z = solve3([t[0] for t in tri], [t[1] for t in tri])
        if z is None or any(abs(v) > 1 for v in z):
            continue
        verts.add(tuple(z))
    best = None
    for z in verts:
        B = matvec(M, z)
        for mu in (Fr(0), Fr(1)):
            s = Q * (1 + mu) / q * Delta - sum(hcell(Q, mu, A[i], B[i]) for i in range(3)) / q
            if best is None or s < best[0]:
                best = (s, mu, z)
    return best, len(verts)


def hand_bound(t, P, Q, mu):
    p = P + 1; q = Q + 1
    if t == 'B':
        return (2 / q) * (Q * (1 + mu) * (P - 1) ** 2 - 2 * mu * P * max(Fr(0), p - Q))
    if t == 'C':
        return (4 / q) * (P * P + 1 - mu * (P - 1))
    if t == 'E':
        return (8 * P / q) * (P - mu)
    return Fr(0)


def min_with_bound(P, Q, c, t):
    """exact min of s - hand_bound over cube x [0,1] (both affine in mu for fixed zeta -> mu endpoints suffice,
    except the (p-Q)^+ term which is constant in mu)."""
    p = P + 1; q = Q + 1
    M = T(2, p); A = matvec(M, c); Delta = d_def(2, p) - l1(A)
    planes = []
    for k in range(3):
        e = [0, 0, 0]; e[k] = 1
        planes += [(tuple(e), Fr(1)), (tuple(e), Fr(-1))]
    for i in range(3):
        for beta in {A[i], Fr(0), -Q * A[i]}:
            planes.append((tuple(M[i]), beta))
    best = None
    for tri in itertools.combinations(planes, 3):
        z = solve3([t_[0] for t_ in tri], [t_[1] for t_ in tri])
        if z is None or any(abs(v) > 1 for v in z):
            continue
        B = matvec(M, z)
        for mu in (Fr(0), Fr(1)):
            s = Q * (1 + mu) / q * Delta - sum(hcell(Q, mu, A[i], B[i]) for i in range(3)) / q
            d = s - hand_bound(t, P, Q, mu)
            if best is None or d < best:
                best = d
    return best


# ---------------- in-range exact minimisation ----------------
eps = Fr(1, 1000)
Ps_big = [Fr(4), 4 + eps, Fr(9, 2), Fr(5), Fr(6), Fr(10), Fr(37, 3), Fr(50), Fr(1000)]
Qs_big = [Fr(2), 2 + eps, Fr(5, 2), Fr(3), Fr(4), Fr(6), Fr(10), Fr(100), Fr(1000)]
Qs_p3 = [Fr(4), 4 + eps, Fr(9, 2), Fr(5), Fr(6), Fr(10), Fr(40), Fr(100), Fr(1000)]
grid = [(P, Q) for P in Ps_big for Q in Qs_big] + [(Fr(2), Q) for Q in Qs_p3]
allc = list(itertools.product((1, -1), repeat=3))
worst = {t: None for t in 'ABCE'}
nviol = 0
for (P, Q) in grid:
    for c in allc:
        t = next(k for k, v in TYPES.items() if v == c or tuple(-x for x in v) == c)
        (s, mu, z), nv = exact_min(P, Q, c)
        if t == 'A':
            if s != 0:
                nviol += 1; log(f"VIOLATION type A: P={P} Q={Q} c={c} min s = {s}")
        else:
            if s <= 0:
                nviol += 1; log(f"VIOLATION type {t}: P={P} Q={Q} c={c} min s = {s} at mu={mu} zeta={z}")
            dmin = min_with_bound(P, Q, c, t)
            if dmin < 0:
                nviol += 1; log(f"HAND BOUND FAILS type {t}: P={P} Q={Q} c={c}: min(s - bound) = {dmin}")
        r = s * (Q + 1)  # normalised
        if worst[t] is None or r < worst[t][0]:
            worst[t] = (r, P, Q, c, mu, z)
log(f"exact cube minimisation over {len(grid)} (P,Q) pairs (incl. boundaries P=4,Q=2 / P=2,Q=4 and +1/1000), 8 columns each:"
    f" violations of Lemma S or of the hand bounds: {nviol}")
for t in 'ABCE':
    r, P, Q, c, mu, z = worst[t]
    log(f"  type {t}: smallest q*min s = {r} (={float(r):.6g}) at P={P}, Q={Q}, c={c}, mu={mu}, zeta={tuple(str(v) for v in z)}")

# ---------------- symbolic check of the inequalities used in the hand proof ----------------
P, Q, s_, t_, mu = sp.symbols('P Q s t mu', nonnegative=True)
p = P + 1
claims = {
    'A1: Q*2P^2 - 2pP >= 0': Q * 2 * P ** 2 - 2 * p * P,
    'A2: Q(P^2+1) - p^2 >= 0': Q * (P ** 2 + 1) - p ** 2,
    'B2: Q(p^2-2) - p^2 >= 0': Q * (p ** 2 - 2) - p ** 2,
    'C2: Q(P^2-1) - p^2 >= 0 (> 0)': Q * (P ** 2 - 1) - p ** 2,
    'E/C: Q(1+mu)(P^2+1) - 2 mu p P - 2[P^2+1-mu(P-1)] >= 0': Q * (1 + mu) * (P ** 2 + 1) - 2 * mu * p * P - 2 * (P ** 2 + 1 - mu * (P - 1)),
    'E: Q(1+mu)P^2 - 2mu pP - 2P(P-mu) >= 0': Q * (1 + mu) * P ** 2 - 2 * mu * p * P - 2 * P * (P - mu),
}
def nonneg_on(expr, region):
    if region == 'big':
        e = sp.expand(expr.subs({P: 4 + s_, Q: 2 + t_}, simultaneous=True))
    else:
        e = sp.expand(expr.subs({P: 2, Q: 4 + t_}, simultaneous=True))
    poly = sp.Poly(e, s_, t_, mu)
    # mu in [0,1]: substitute mu = u/(1+u)? simpler: expression is affine in mu -> check at mu=0 and mu=1
    ok = True
    for mv in (0, 1):
        pe = sp.Poly(sp.expand(e.subs(mu, mv)), s_, t_)
        if any(cf < 0 for cf in pe.coeffs()):
            ok = False
    return ok, e
for name, expr in claims.items():
    for reg in ('big', 'p3'):
        assert sp.degree(sp.expand(expr), mu) <= 1
        ok, e = nonneg_on(expr, reg)
        log(f"  hand-proof inequality {name} [{reg}]: {'OK (all coefficients >= 0 at mu=0,1; affine in mu)' if ok else 'NOT certified by coefficients'}")
# type B bracket at mu=1 for Q < p, P>=4:  2Q(P-1)^2 - 2P(P+1-Q) >= 2(P-1)(P-2) > 0 and increasing in Q
br = 2 * Q * (P - 1) ** 2 - 2 * P * (P + 1 - Q)
assert sp.expand(br.subs(Q, 2) - 2 * (P - 1) * (P - 2)) == 0
assert sp.expand(sp.diff(br, Q) - (2 * (P - 1) ** 2 + 2 * P)) == 0
log("  type B bracket at mu=1: equals 2(P-1)(P-2) at Q=2, dQ = 2(P-1)^2+2P > 0: OK")

# ---------------- informative: outside the stated range ----------------
log("Outside the stated range (informative only):")
for (P, Q) in [(Fr(3), Fr(2)), (Fr(2), Fr(3)), (Fr(2), Fr(2)), (Fr(1), Fr(4)), (Fr(3, 2), Fr(2)), (Fr(4), Fr(3, 2)), (Fr(2), Fr(7, 2))]:
    msgs = []
    for t, c in TYPES.items():
        (s, mu, z), nv = exact_min(P, Q, c)
        msgs.append(f"{t}:{float(s):.4g}")
    log(f"  P={P} Q={Q}: exact min s per type " + ' '.join(msgs))
log("DONE")
