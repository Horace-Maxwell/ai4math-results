"""(1) Strict re-certification of all FD1/FD2 vertex checks of prove_fd.py, additionally requiring every denominator factor to
have nonnegative coefficients AND a positive constant term; (2) 42 000 random interior points of the FD1 parameter boxes,
evaluated exactly with the true min/max closed forms of formulas.py."""
import sympy as sp, random
from fractions import Fraction as Fr
import prove_fd as pf
from formulas import s_formula_FD1
P, Q, s, t = pf.P, pf.Q, pf.s, pf.t
def certify_strict(expr, region):
    e = expr.subs({P: 4 + s, Q: 2 + t}, simultaneous=True) if region == 'big' else expr.subs({P: 2, Q: 4 + t}, simultaneous=True)
    num, den = sp.fraction(sp.together(sp.expand(e)))
    dfac = sp.factor_list(den); sign = sp.sign(dfac[0])
    for f, k in dfac[1]:
        pf_ = sp.Poly(f, s, t); cs = dict(zip(pf_.monoms(), pf_.coeffs()))
        if all(c >= 0 for c in cs.values()) and cs.get((0, 0), 0) > 0: continue
        if all(c <= 0 for c in cs.values()) and cs.get((0, 0), 0) < 0: sign *= (-1) ** k; continue
        return False, f
    num = sp.expand(sign * num); pn = sp.Poly(num, s, t)
    cs = dict(zip(pn.monoms(), pn.coeffs()))
    return (cs.get((0, 0), 0) > 0 and all(v >= 0 for v in cs.values())), num
pf.certify = certify_strict
pf.results.clear(); pf.run_FD1(); pf.run_FD2()
print("strict re-certification:", len(pf.results), "checks, failures:", sum(1 for r in pf.results if not r[1]))
random.seed(3)
def rnd(lo, hi): u = Fr(random.randint(0, 10**6), 10**6); return lo + (hi - lo) * u
bad = 0; n = 0
for trial in range(1500):
    if trial % 2: Pv = Fr(4) + Fr(random.randint(0, 500), 10); Qv = Fr(2) + Fr(random.randint(0, 500), 10)
    else: Pv = Fr(2); Qv = Fr(4) + Fr(random.randint(0, 500), 10)
    qv = Qv + 1; mu0 = (Qv - 1) / qv; mu1 = (Qv**2 + 1) / qv**2; L = Qv / (qv + 1); dl = Pv**2 + 1
    for dev in ['Asame', 'Bsame', 'Bopp', 'Csame', 'Copp', 'Esame', 'Eopp']:
        m = rnd(mu0, L); E0 = s_formula_FD1(Pv, Qv, Fr(1), m, dev) - 2 * dl * (Qv - m) / qv
        mu = rnd(mu0, L); E1 = s_formula_FD1(Pv, Qv, mu, Fr(1), dev) - 2 * dl * (Qv - mu) / qv
        mu = rnd(L, mu1); m = rnd(mu0, L); E2a = s_formula_FD1(Pv, Qv, mu, m, dev) - 2 * dl * mu
        mu = rnd(mu0, L); m = rnd(L, mu1); E2b = s_formula_FD1(Pv, Qv, mu, m, dev) - 2 * dl * m
        for E in (E0, E1, E2a, E2b):
            n += 1; bad += (E <= 0)
print(f"random interior samples of FD1 boxes: {n}, nonpositive: {bad}")
