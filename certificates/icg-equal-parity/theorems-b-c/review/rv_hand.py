"""Item 5/6 hand proofs, line by line (sympy, exact), plus the two tightness families of §7.
"""
import sys
from fractions import Fraction as Fr
import sympy as sp
from rv_common import T, G, Theta, d_closed, delta_closed, pot, S2

out = []
def log(s):
    print(s); sys.stdout.flush(); out.append(s)

P, Q, s, t, mu, m = sp.symbols('P Q s t mu m', nonnegative=True)
q = Q + 1; p = P + 1
mu0 = (Q - 1) / q; mu1 = (Q ** 2 + 1) / q ** 2; L = Q / (Q + 2)
Dp = 5 * P ** 2 + 2 * P + 1; dp = P ** 2 + 1


def nonneg(expr, region):
    e = expr.subs({P: 4 + s, Q: 2 + t}, simultaneous=True) if region == 'big' else expr.subs({P: 2, Q: 4 + t}, simultaneous=True)
    num, den = sp.fraction(sp.cancel(sp.together(sp.expand(e))))
    pn = sp.Poly(sp.expand(num), s, t); pd = sp.Poly(sp.expand(den), s, t)
    sd = 1 if all(c >= 0 for c in pd.coeffs()) else (-1 if all(c <= 0 for c in pd.coeffs()) else None)
    if sd is None:
        return None
    cs = [sd * c for c in pn.coeffs()]
    const = sd * pn.as_expr().subs({s: 0, t: 0})
    return all(c >= 0 for c in cs), const


# --- A same ---
assert sp.expand(Dp - 5 * dp - 2 * (P - 2)) == 0
assert sp.expand(5 * (Q - 1) ** 2 - (Q ** 2 + 1) - 2 * (2 * Q - 1) * (Q - 2)) == 0
e = (Q - 1) ** 2 * Dp - (Q ** 2 + 1) * dp
r = [nonneg(e, reg) for reg in ('big', 'p3')]
log(f"A same: D_p - 5(P^2+1) = 2(P-2), 5(Q-1)^2-(Q^2+1) = 2(2Q-1)(Q-2); (Q-1)^2 D_p - (Q^2+1)(P^2+1) nonneg coeffs/const: {r}")
log(f"   equality point P=Q=2: {sp.simplify(e.subs({P: 2, Q: 2}))} (excluded: P=2 forces Q>=4)")
# R0 monotone in m, value at m = mu0 equals 2(mu0^2 D_p - mu1 delta_p)
fR0 = 2 * mu0 * m * Dp - 2 * dp * (Q - m) / q
assert sp.simplify(sp.diff(fR0, m) - (2 * mu0 * Dp + 2 * dp / q)) == 0
assert sp.simplify(fR0.subs(m, mu0) - 2 * (mu0 ** 2 * Dp - mu1 * dp)) == 0
log("A same R0: increasing in m and equal to 2(mu0^2 D_p - mu1 delta_p) at m = mu0: OK")
assert sp.simplify(L - sp.Rational(1, 2) - (Q - 2) / (2 * (Q + 2))) == 0
assert nonneg(Dp - 2 * dp, 'big')[0] and nonneg(Dp - 2 * dp, 'p3')[0]
log("A same R2 odd J: L >= 1/2 iff Q >= 2; D_p > 2 delta_p: OK")

# --- C opp ---
bracket = dp * (Q * (1 + mu) - q * sp.Symbol('rho')) - 2 * mu * p * P * m
rho = sp.Symbol('rho')
full = 2 * dp * Q * (1 + mu) / q - 4 * mu * p * P * m / q - 2 * dp * rho
assert sp.simplify(full - (2 / q) * bracket) == 0
R0 = sp.expand(bracket.subs({mu: 1, rho: (Q - m) / q}))
assert sp.expand(R0 - (dp * Q - m * (P ** 2 + 2 * P - 1))) == 0
R1 = sp.expand(bracket.subs({m: 1, rho: (Q - mu) / q}))
assert sp.expand(R1 - mu * (dp * q - 2 * p * P)) == 0
assert sp.expand(dp * 3 - 2 * p * P - (P ** 2 - 2 * P + 3)) == 0
log("C opp: s - 2 delta_p rho = (2/q)[(P^2+1)(Q(1+mu)-q rho) - 2 mu pPm]; R0 = (P^2+1)Q - m(P^2+2P-1); "
    "R1 = mu[(P^2+1)q - 2pP] >= mu(P^2-2P+3): OK")
# R2: Q >= (18/5) mu1 for Q >= 2, and (18/5)(P^2+1) > 2(P^2+P)
e1 = sp.expand((5 * Q * (Q + 1) ** 2 - 18 * (Q ** 2 + 1)).subs(Q, 2 + t))
assert all(c >= 0 for c in sp.Poly(e1, t).coeffs())
e2 = sp.expand(18 * (P ** 2 + 1) - 10 * (P ** 2 + P))
assert sp.discriminant(e2, P) < 0
log(f"C opp R2: 5Q(Q+1)^2 - 18(Q^2+1) at Q=2+t = {e1} (>= 0); 18(P^2+1) - 10(P^2+P) = {e2} has negative discriminant: OK")

# --- E opp ---
lhs = 4 * P * (P * Q - 1) * (Q + 1) - 2 * (P ** 2 + 1) * (Q ** 2 + 1)
dec = P * Q * (P * Q - 4) + Q ** 2 * (P ** 2 - 2) + (4 * P ** 2 * Q - 2 * P ** 2 - 4 * P - 2)
assert sp.expand(lhs - dec) == 0
r = [nonneg(lhs, reg) for reg in ('big', 'p3')]
# the lower bound PQ(1+mu) - mu(2P+1) m >= PQ - 1 for mu, m in [0,1]
f = P * Q * (1 + mu) - mu * (2 * P + 1)
okb = all(nonneg(f.subs(mu, mv) - (P * Q - 1), reg)[0] for mv in (0, 1) for reg in ('big', 'p3'))
log(f"E opp: decomposition identity OK; 4P(PQ-1)(Q+1) - 2(P^2+1)(Q^2+1) nonneg coeffs/const: {r}; "
    f"PQ(1+mu) - mu(2P+1) >= PQ-1 on mu in [0,1]: {okb}")

# --- FD2 (b) J' = -1 ---
x = sp.symbols('x', positive=True)
assert sp.simplify((3 * x - 4) / x - 3 * ((x - 1) ** 2 + 1) / x ** 2 - (2 * x - 6) / x ** 2) == 0
for qq in (5, 7, Fr(9, 2), 11, 101):
    qq = Fr(qq); mu_ = pot(40, qq)
    for b in range(2, 31, 2):
        Dh = d_closed(b, qq) / qq ** b; rho_ = mu_[b - 1]
        Dh1 = d_closed(b - 1, qq) / qq ** (b - 1)
        assert Dh - 5 * rho_ == Dh1 - 3 * rho_
        assert Dh1 >= d_closed(1, qq) / qq and rho_ <= mu_[1]
        assert Dh - 5 * rho_ >= (2 * qq - 6) / qq ** 2 > 0
log("FD2(b) J'=-1: (3q-4)/q - 3 mu1 = (2q-6)/q^2; D_b - 5 rho = D_(b-1) - 3 rho >= (2q-6)/q^2 > 0 (b<=30, 5 q's): OK")

# --- FD2(a) chain column P>=4 ---
fch = (2 / q) * ((P - 1) ** 2 * Q * (1 + mu) - 2 * P * (Q - mu))
assert sp.simplify(sp.diff(fch, mu) - (2 / q) * ((P - 1) ** 2 * Q + 2 * P)) == 0
v = sp.simplify(fch.subs(mu, mu0))
assert sp.simplify(v - 4 / q ** 2 * ((P - 1) ** 2 * Q ** 2 - P * (Q ** 2 + 1))) == 0
g = (P - 1) ** 2 * Q ** 2 - P * (Q ** 2 + 1) - (4 * P ** 2 - 13 * P + 4)
log(f"FD2(a) chain column: increasing in mu; value at mu0 = (4/q^2)[(P-1)^2Q^2 - P(Q^2+1)] (text writes 4/q); "
    f"[(P-1)^2Q^2 - P(Q^2+1)] - (4P^2-13P+4) nonneg on P>=4,Q>=2: {nonneg(g, 'big')}; 4P^2-13P+4 at P=4: {4*16-13*4+4}")

# --- tightness families (§7) ---
for pp in (5, 7, 11, 101):
    Y = [[1, 1, -1], [-1, -1, 1], [1, 1, -1]]   # s_2 (1,1,-1)^T
    assert Theta(2, 2, pp, 3) - G(Y, pp, 3) == 4 * (pp - 3)
log("horizontal rank-one Y = s_2(1,1,-1)^T, (2,2), q=3: Theta - G = 4(p-3) for p in {5,7,11,101}: OK")
for qq in (5, 7, 11, Fr(9, 2)):
    for b in (2, 4, 6, 8):
        sb = [(-1) ** j for j in range(b + 1)]
        Y = [[1 * x_ for x_ in sb], [1 * x_ for x_ in sb], [-1 * x_ for x_ in sb]]
        assert Y[2][b] == -1
        gap = Theta(2, b, 3, qq) - G(Y, 3, qq)
        assert gap == 2 * (d_closed(b, qq) - 5 * delta_closed(b, qq))
        if b == 2:
            assert gap == 4 * (Fr(qq) - 3)
log("vertical rank-one Y = (1,1,-1)^T s_b^T, p=3: Theta - G = 2(d_b(q) - 5 delta_b(q)) (b=2,4,6,8), = 4(q-3) at b=2: OK")
# --- negative control: odd b (opposite parity) -- the checkerboard s_2 s_b^T is admissible there and beats Theta
from rv_common import d_def
for b in (1, 3, 5):
    for (pp, qq) in ((5, 3), (3, 5), (7, 3)):
        Y = [[(-1) ** (i + j) for j in range(b + 1)] for i in range(3)]
        assert Y[2][b] == -1
        assert G(Y, pp, qq) == d_def(2, pp) * d_def(b, qq) > Theta(2, b, pp, qq)
log("negative control, odd b in {1,3,5}: the checkerboard is admissible and G = d_2 d_b > Theta, so Theorem B' is false for odd b "
    "(b even is essential: it makes the corner of s_2 s_b^T equal +1).")
log("DONE")
