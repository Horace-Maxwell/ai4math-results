"""Third, symbolic implementation of the Roldan certificates (SymPy, exact).

Builds the weighted Ramanujan entries directly from the prime-power
Ramanujan-sum rule as polynomials in symbols p, q, then
  (1) bivariate certificate in x=p-3, y=q-3 over all 2048 masks;
  (2) univariate q=3 certificate in t=p-5 over all 2048 masks;
  (3) D* energy polynomial vs Jiang-Yang closed form (1/2)[n + d_2(p) d_3(q)].
Compares (1) with the saved CSV of the first implementation.
"""
import csv, json, hashlib
from pathlib import Path
import sympy as sp

p, q, x, y, t = sp.symbols("p q x y t")

def ram(l, k, a):  # c_{l^k}(l^a), symbolic prime l
    if k == 0:
        return sp.Integer(1)
    if k <= a:
        return l**k - l**(k - 1)
    if k == a + 1:
        return -l**a
    return sp.Integer(0)

def totient_pp(l, k):
    return sp.Integer(1) if k == 0 else l**k - l**(k - 1)

rows = [(a, b) for a in range(3) for b in range(4)]
cols = [(c, d) for c in range(3) for d in range(4) if (c, d) != (2, 3)]
STAR = {(0, 0), (2, 0), (1, 1), (0, 2), (2, 2), (1, 3)}
star_mask = sum(1 << j for j, cd in enumerate(cols) if cd in STAR)
assert star_mask == 1445

W = [[sp.expand(totient_pp(p, 2 - a) * totient_pp(q, 3 - b) * ram(p, 2 - c, a) * ram(q, 3 - d, b))
      for (c, d) in cols] for (a, b) in rows]

# (1) bivariate, x=p-3, y=q-3
Wxy = [[sp.Poly(sp.expand(w.subs({p: x + 3, q: y + 3})), x, y) for w in row] for row in W]
def coeffs_xy(poly):
    return {(i, j): int(poly.coeff_monomial(x**i * y**j)) for i in range(3) for j in range(4)}
assert all(Wxy[r][c].degree(x) <= 2 and Wxy[r][c].degree(y) <= 3 for r in range(12) for c in range(11))
Cxy = [[coeffs_xy(Wxy[r][c]) for c in range(11)] for r in range(12)]
keys = [(i, j) for i in range(3) for j in range(4)]

def envelope_xy(mask):
    U = {k: 0 for k in keys}
    signs_ok = True
    for r in range(12):
        row = {k: sum(Cxy[r][c][k] for c in range(11) if mask >> c & 1) for k in keys}
        vals = list(row.values())
        if not (all(v >= 0 for v in vals) or all(v <= 0 for v in vals)):
            signs_ok = False
        for k in keys:
            U[k] += abs(row[k])
    return U, signs_ok

Pstar, ok = envelope_xy(star_mask)
assert ok, "D* rows must have one-signed coefficients"
min_gap = {k: None for k in keys}
gaps = {}
for mask in range(2048):
    U, _ = envelope_xy(mask)
    g = {k: Pstar[k] - U[k] for k in keys}
    assert all(v >= 0 for v in g.values()), (mask, g)
    gaps[mask] = [g[k] for k in keys]
    if mask != star_mask:
        assert g[(0, 0)] > 0
        for k in keys:
            min_gap[k] = g[k] if min_gap[k] is None else min(min_gap[k], g[k])

# compare with first implementation's CSV
here = Path(__file__).resolve().parent
csv_path = next(c for c in [here / "circulant-coefficient-gaps.csv",
                            here.parents[1] / "round2/fresh-hunt/circulant-coefficient-gaps.csv"] if c.exists())
with csv_path.open() as f:
    rd = csv.reader(f); next(rd)
    saved = {int(r[0]): [int(v) for v in r[1:]] for r in rd}
assert saved == gaps, "mismatch with first implementation"

# (3) closed form
def d_k(k, z):
    return (2 * k + 1) * z**k + 4 * sum((-1)**(k - j) * (j + 1) * z**j for j in range(k))
jy = sp.expand(sp.Rational(1, 2) * (p**2 * q**3 + d_k(2, p) * d_k(3, q)))
star_poly = sp.expand(sum(Pstar[(i, j)] * (p - 3)**i * (q - 3)**j for (i, j) in keys))
assert sp.expand(star_poly - jy) == 0
roldan = sp.expand((5*p*p - 8*p + 4)*(q - 1)*(3*q*q - 2*q + 1) + (p - 1)*(2*p - 1)*(q**3 - 2*q*q + 2*q - 2)
                   + (p*p - 2*p + 2)*(q - 1)*(q*q + 1) + (p - 1)*q**3)
assert sp.expand(star_poly - roldan) == 0

# (2) q = 3, t = p-5
Wt = [[sp.Poly(sp.expand(w.subs({q: 3, p: t + 5})), t) for w in row] for row in W]
Ct = [[[int(Wt[r][c].coeff_monomial(t**k)) for k in range(3)] for c in range(11)] for r in range(12)]
def envelope_t(mask):
    U = [0, 0, 0]; ok = True
    for r in range(12):
        row = [sum(Ct[r][c][k] for c in range(11) if mask >> c & 1) for k in range(3)]
        if not (all(v >= 0 for v in row) or all(v <= 0 for v in row)):
            ok = False
        U = [U[k] + abs(row[k]) for k in range(3)]
    return U, ok
St, ok = envelope_t(star_mask)
assert ok and St == [4832, 2256, 266]
mg = [None] * 3; arg = None
for mask in range(2048):
    if mask == star_mask:
        continue
    U, _ = envelope_t(mask)
    g = [St[k] - U[k] for k in range(3)]
    assert all(v >= 0 for v in g) and g[0] > 0
    mg = [g[k] if mg[k] is None else min(mg[k], g[k]) for k in range(3)]
assert mg == [408, 192, 24]
argmins = [[m for m in range(2048) if m != star_mask and St[k] - envelope_t(m)[0][k] == mg[k]] for k in range(3)]
assert argmins == [[1957], [1957], [1957]]  # D* plus the divisor 3p^2 (pair (2,1), bit 9)
assert sp.expand(sum(St[k] * (p - 5)**k for k in range(3)) - (266*p**2 - 404*p + 202)) == 0

# Lean table cross-check: the basisCoeff table in Research/CirculantQ3.lean
lean_path = next(c for c in [here.parent / "lean/Research/CirculantQ3.lean",
                             here.parents[1] / "lean/Research/CirculantQ3.lean",
                             here.parents[1] / "research-lean/Research/CirculantQ3.lean"] if c.exists())
lean_src = lean_path.read_text()
import re
blk = lean_src.split("def basisCoeff")[1].split("def chosen")[0]
nums = [int(v) for v in re.findall(r"-?\d+", blk.split(":=", 1)[1])]
assert nums == [Ct[r][c][k] for r in range(12) for c in range(11) for k in range(3)], "Lean table mismatch"

out = {"bivariate_star_coefficients_x_i_y_j": [Pstar[k] for k in keys],
       "bivariate_min_gap": [min_gap[k] for k in keys],
       "matches_first_implementation_csv": True,
       "star_poly_equals_JiangYang_and_Roldan_closed_forms": True,
       "q3_star_coefficients_t": St, "q3_min_gap_t": mg, "q3_argmin_masks": argmins,
       "lean_basisCoeff_table_matches": True,
       "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name("bivariate_sympy_check.json").write_text(json.dumps(out, indent=2))
print(json.dumps(out))
