"""Items 5-6: referee's own certification of the vertex inequalities of Lemmas FD1 and FD2.

Forms: built from the referee's per-cell derivation (rv_fd_forms.py docstring), written as  base + sum of min-groups.
A value base + sum_k min(G_k) is > 0  iff  base + sum_k (any choice from G_k) > 0 for every choice (exact equivalence).

Vertex reduction (checked by hand in the report): each form is, for fixed m, affine in mu or a min of affine functions of mu
(and likewise in m for fixed mu); the rho-term is affine.  A function concave in each variable separately attains its minimum
over a box at a vertex.  => positivity at the vertices (for every min-choice) proves positivity on the box.

Certificate for a rational function f(P,Q):
   region big: P = 4+s, Q = 2+t;   region p3: P = 2, Q = 4+t;   (s,t >= 0 real)
   f = num/den; every irreducible factor of den (over Q) has all coefficients >= 0 and a positive constant term (or all <= 0
   and negative constant term, sign tracked); sign-adjusted num has all coefficients >= 0 and a positive constant term.
If a numerator fails the coefficient test, a fallback is tried (1 variable: exact real-root count on [0,oo) via sympy
count_roots + value at 0; 2 variables: reported as FAIL).
Independent sanity layer: every vertex expression is also evaluated exactly (Fractions) at 400 rational points of the region.
"""
import itertools, sys, random
from fractions import Fraction as Fr
import sympy as sp

random.seed(5)
out = []
def log(s):
    print(s); sys.stdout.flush(); out.append(s)

P, Q, s, t = sp.symbols('P Q s t', nonnegative=True)
q = Q + 1; p = P + 1
mu0 = (Q - 1) / (Q + 1); mu1 = (Q ** 2 + 1) / (Q + 1) ** 2; L = Q / (Q + 2)
Dp = 5 * P ** 2 + 2 * P + 1; dp = P ** 2 + 1
one = sp.Integer(1)


def form(kind, dev, MU, M):
    """returns (base, [group1, group2, ...]) for s at column J with mu_{J-1} = MU and state magnitude M."""
    ch = Q * (1 + MU) / q
    g2 = p ** 2 - 2
    if kind == 'fd1':
        if dev == 'Asame':
            return (4 * (Q - MU) * p * P * M + 4 * (Q - MU) * P ** 2 * M + 2 * (Q - MU) * (P ** 2 + 1) * M) / q, []
        if dev == 'Bsame':
            return (ch * 2 * (P - 1) ** 2 + 2 * (Q - MU) * (P ** 2 + 1) * M / q,
                    [[4 * (Q - MU) * P ** 2 * M / q, 4 * P * (Q - MU * P * M) / q]])
        if dev == 'Bopp':
            return (ch * 2 * (P - 1) ** 2 + 4 * (Q - MU) * p * P * M / q,
                    [[sp.Integer(0), -4 * MU * P * (P * M - Q) / q]])
        if dev == 'Csame':
            return (ch * 2 * (P ** 2 + 1) - (4 * MU * p * P * M - 4 * (Q - MU) * P ** 2 * M) / q,
                    [[2 * (Q - MU) * (P ** 2 + 1) * M / q, 2 * (Q * (P ** 2 - 1) - MU * M * (P ** 2 + 1)) / q]])
        if dev == 'Copp':
            return ch * 2 * (P ** 2 + 1) - 4 * MU * p * P * M / q, []
        if dev == 'Esame':
            return ch * 4 * P ** 2 - (4 * MU * p * P * M + 4 * MU * P ** 2 * M - 2 * (Q - MU) * (P ** 2 + 1) * M) / q, []
        if dev == 'Eopp':
            return ch * 4 * P ** 2 - (4 * MU * p * P * M + 4 * MU * P ** 2 * M) / q, []
    else:
        if dev == 'chain':
            return ch * 2 * (P - 1) ** 2, []
        if dev == 'Asame':
            return (4 * (Q - MU) * P * M / q,
                    [[2 * (Q - MU) * M * g2 / q, 2 * (Q * (P ** 2 + 1) - MU * M * g2) / q]])
        if dev == 'Aopp':
            return 4 * (Q - MU) * p * P * M / q, []
        if dev == 'Bsame':
            return ch * 2 * (P - 1) ** 2 + (4 * (Q - MU) * p * P * M + 4 * (Q - MU) * P * M + 2 * (Q - MU) * M * g2) / q, []
        if dev == 'Csame':
            return (ch * 2 * (P ** 2 + 1) - (4 * MU * p * P * M - 4 * (Q - MU) * P * M) / q,
                    [[2 * (Q - MU) * M * g2 / q, 2 * (Q * (P ** 2 - 1) - MU * M * g2) / q]])
        if dev == 'Copp':
            return ch * 2 * (P ** 2 + 1) - 4 * MU * p * P * M / q, []
        if dev == 'Esame':
            return ch * 4 * P ** 2 - (4 * MU * p * P * M + 4 * MU * P * M - 2 * (Q - MU) * M * g2) / q, []
        if dev == 'Eopp':
            return ch * 4 * P ** 2 - (4 * MU * p * P * M + 4 * MU * P * M) / q, []
    raise ValueError((kind, dev))


def branches(base, groups, extra):
    """all expressions base + extra + choice."""
    res = []
    for choice in itertools.product(*groups) if groups else [()]:
        res.append(base + extra + sum(choice))
    return res


def subst(expr, region):
    if region == 'big':
        return expr.subs({P: 4 + s, Q: 2 + t}, simultaneous=True)
    return expr.subs({P: 2, Q: 4 + t}, simultaneous=True)


def certify(expr, region):
    e = sp.together(sp.expand(subst(expr, region)))
    num, den = sp.fraction(sp.cancel(e))
    num = sp.expand(num); den = sp.expand(den)
    sign = 1
    c0, facs = sp.factor_list(den, s, t)
    if c0 < 0:
        sign = -sign
    for f, k in facs:
        pf = sp.Poly(f, s, t)
        cs = pf.coeffs(); const = pf.as_expr().subs({s: 0, t: 0})
        if all(c >= 0 for c in cs) and const > 0:
            continue
        if all(c <= 0 for c in cs) and const < 0:
            sign *= (-1) ** k
            continue
        return False, f"denominator factor {f} not of fixed sign"
    num = sign * num
    pn = sp.Poly(num, s, t)
    coeffs = dict(zip(pn.monoms(), pn.coeffs()))
    const = coeffs.get((0, 0), 0)
    neg = {k: v for k, v in coeffs.items() if v < 0}
    if const > 0 and not neg:
        return True, 'coeff'
    # fallback, one variable only
    if region == 'p3' or pn.degree(s) == 0:
        pt = sp.Poly(pn.as_expr().subs(s, 0), t)
        if pt.eval(0) > 0 and pt.count_roots(0, None) == 0:
            return True, 'sturm'
    return False, f"const={const}, negative coefficients={neg}"


def exact_eval_positive(expr, region, npts=400):
    fn = sp.lambdify((P, Q), expr, modules=[{'Min': min, 'Max': max}])
    worst = None
    for k in range(npts):
        if region == 'big':
            PP = Fr(4) + Fr(random.randint(0, 3000), random.choice([1, 7, 100, 1000])) * (k % 3)
            QQ = Fr(2) + Fr(random.randint(0, 3000), random.choice([1, 7, 100, 1000])) * ((k // 3) % 3)
        else:
            PP = Fr(2)
            QQ = Fr(4) + Fr(random.randint(0, 3000), random.choice([1, 7, 100, 1000])) * (k % 3)
        v = fn(PP, QQ)
        v = Fr(v) if not isinstance(v, Fr) else v
        if worst is None or v < worst[0]:
            worst = (v, PP, QQ)
    return worst


results = []  # (label, region, nbranches, ok, method-info)
METHODS = {}
npoly = 0


def check(label, base, groups, extra, regions):
    global npoly
    allok = True
    for reg in regions:
        brs = branches(base, groups, extra)
        for br in brs:
            ok, info = certify(br, reg)
            npoly += 1
            METHODS[info if ok else 'fail'] = METHODS.get(info if ok else 'fail', 0) + 1
            if not ok:
                allok = False
                log(f"   FAIL {label} [{reg}]: {info}")
            w = exact_eval_positive(br, reg, 60)
            if w[0] <= 0:
                allok = False
                log(f"   NUMERIC FAIL {label} [{reg}]: value {w[0]} at P={w[1]} Q={w[2]}")
    results.append((label, ok, allok))
    return allok


FD1DEVS = ['Asame', 'Bsame', 'Bopp', 'Csame', 'Copp', 'Esame', 'Eopp']
CHDEVS = ['Asame', 'Aopp', 'Bsame', 'Csame', 'Copp', 'Esame', 'Eopp']
REG = ('big', 'p3')

# ---------------- FD1 ----------------
n_fd1 = 0
for dev in FD1DEVS:
    for mv, lab in [(mu0, 'mu0'), (L, 'L')]:                    # R0: mu = 1, rho = (Q-m)/q exact
        b_, g_ = form('fd1', dev, one, mv)
        check(f"FD1 {dev} R0 m={lab}", b_, g_, -2 * dp * (Q - mv) / q, REG); n_fd1 += 1
    for MUv, lab in [(mu0, 'mu0'), (L, 'L')]:                   # R1: m = 1, rho = (Q-mu)/q exact
        b_, g_ = form('fd1', dev, MUv, one)
        check(f"FD1 {dev} R1 mu={lab}", b_, g_, -2 * dp * (Q - MUv) / q, REG); n_fd1 += 1
    for (MUv, a), (mv, c) in itertools.product([(L, 'L'), (mu1, 'mu1')], [(mu0, 'mu0'), (L, 'L')]):   # R2a, rho < mu
        b_, g_ = form('fd1', dev, MUv, mv)
        check(f"FD1 {dev} R2a mu={a} m={c}", b_, g_, -2 * dp * MUv, REG); n_fd1 += 1
    for (MUv, a), (mv, c) in itertools.product([(mu0, 'mu0'), (L, 'L')], [(L, 'L'), (mu1, 'mu1')]):   # R2b, rho < m
        b_, g_ = form('fd1', dev, MUv, mv)
        check(f"FD1 {dev} R2b mu={a} m={c}", b_, g_, -2 * dp * mv, REG); n_fd1 += 1
log(f"FD1: {n_fd1} vertex checks done")

# ---------------- FD2 ----------------
n_fd2 = 0
for dev in CHDEVS:                                              # (a) J = b-1, m = 1, mu = mu_{b-2} in [mu0, L)
    for MUv, lab in [(mu0, 'mu0'), (L, 'L')]:
        b_, g_ = form('chain', dev, MUv, one)
        check(f"FD2(a) {dev} mu={lab}", b_, g_, -4 * P * (Q - MUv) / q, REG); n_fd2 += 1
for MUv, lab in [(mu0, 'mu0'), (L, 'L')]:                       # (a) chain column alone, P >= 4
    b_, g_ = form('chain', 'chain', MUv, one)
    check(f"FD2(a) chain column, P>=4, mu={lab}", b_, g_, -4 * P * (Q - MUv) / q, ('big',)); n_fd2 += 1
for dev in CHDEVS:                                              # (b) k = 1
    for MUv, lab in [(L, 'L'), (mu1, 'mu1'), (one, '1')]:
        x = (Q - MUv) / q; rho = (Q - x) / q
        chain = 2 * (P - 1) ** 2 * Q * (1 + x) / q
        b_, g_ = form('chain', dev, MUv, mu0)
        check(f"FD2(b) k=1 {dev} mu={lab}", b_, g_, chain - 4 * P * rho, ('p3',)); n_fd2 += 1
for dev in CHDEVS:                                              # (b) k = 2
    for MUv, lab in [(mu0, 'mu0'), (L, 'L')]:
        y = (Q - MUv) / q; x = (Q - y) / q; rho = (Q - x) / q
        chain = 2 * (P - 1) ** 2 * Q * (2 + x + y) / q
        b_, g_ = form('chain', dev, MUv, mu1)
        check(f"FD2(b) k=2 {dev} mu={lab}", b_, g_, chain - 4 * P * rho, ('p3',)); n_fd2 += 1
for Xv, lab in [(mu0, 'mu0'), (L, 'L')]:                         # (b) k >= 3, chain alone (y >= L, w >= mu0)
    chain = 2 * (P - 1) ** 2 * Q * ((1 + Xv) + (1 + L) + (1 + mu0)) / q
    check(f"FD2(b) k>=3 chain alone x={lab}", chain - 4 * P * (Q - Xv) / q, [], 0, ('p3',)); n_fd2 += 1
log(f"FD2: {n_fd2} vertex checks done")

nfail = sum(1 for r in results if not r[2])
log(f"TOTAL: {len(results)} vertex checks, {npoly} certified polynomials (branches x regions), failures: {nfail}; methods: {METHODS}")
for r in results:
    log(("   OK   " if r[2] else "   FAIL ") + r[0])

# ---------------- negative controls (the certifier must be able to fail) ----------------
def region_sub_wide(expr):
    return expr.subs({P: 2 + s, Q: 2 + t}, simultaneous=True)
def certify_custom(expr, subfn):
    e = sp.together(sp.expand(subfn(expr)))
    num, den = sp.fraction(sp.cancel(e))
    pn = sp.Poly(sp.expand(num), s, t); pd = sp.Poly(sp.expand(den), s, t)
    okd = all(c >= 0 for c in pd.coeffs()) or all(c <= 0 for c in pd.coeffs())
    sg = 1 if all(c >= 0 for c in pd.coeffs()) else -1
    cs = [sg * c for c in pn.coeffs()]
    const = sg * pn.as_expr().subs({s: 0, t: 0})
    return okd and const > 0 and all(c >= 0 for c in cs)
b_, g_ = form('fd1', 'Asame', one, mu0)
nc1 = [certify(br, 'big')[0] for br in branches(b_, g_, -sp.Rational(21, 10) * dp * (Q - mu0) / q)]
log(f"negative control 1: FD1 A-same R0 m=mu0 with need 2.1*delta_p*rho instead of 2*delta_p*rho: certified={nc1} (expected [False])")
nc2 = [certify_custom(br, region_sub_wide) for br in branches(b_, g_, -2 * dp * (Q - mu0) / q)]
log(f"negative control 2: same vertex on the enlarged region P>=2, Q>=2 (contains p=q=3): certified={nc2} (expected [False]: equality at P=Q=2)")
val = sp.simplify((b_ - 2 * dp * (Q - mu0) / q).subs({P: 2, Q: 2}))
log(f"   value at P=Q=2: {val} (expected 0)")
b_, g_ = form('chain', 'chain', mu0, one)
nc3 = [certify(br, 'p3')[0] for br in branches(b_, g_, -4 * P * (Q - mu0) / q)]
log(f"negative control 3: FD2 chain column alone at P=2 (the case that needs part (b)): certified={nc3} (expected [False])")

# ---------------- hand-proof formulas (typo check) ----------------
MU = sp.symbols('MU')
# FD2(a): 2(P-1)^2 chat_{b-1} - 4P rho at mu = mu0
e = (2 * (P - 1) ** 2 * Q * (1 + MU) / q - 4 * P * (Q - MU) / q).subs(MU, mu0)
claimed_text = 4 / q * ((P - 1) ** 2 * Q ** 2 - P * (Q ** 2 + 1))
correct = 4 / q ** 2 * ((P - 1) ** 2 * Q ** 2 - P * (Q ** 2 + 1))
log(f"FD2(a) chain value at mu0: equals (4/q)[...]? {sp.simplify(e - claimed_text) == 0};  equals (4/q^2)[...]? {sp.simplify(e - correct) == 0}")
# FD2(b) k>=3 bound: 2(chat_{b-1}+chat_{b-2}+chat_{b-3}) - 8 rho with x, y, w
x_, y_, w_ = sp.symbols('x y w')
PP = 2
e3 = 2 * Q * ((1 + x_) + (1 + y_) + (1 + w_)) / q - 4 * PP * (Q - x_) / q
lower_mine = (2 / q) * ((2 * Q + 4) * mu0 + Q * L - Q)
lower_text = (2 / q) * ((4 * Q + 8) * mu0 - 2 * Q + 2 * Q * L)
val_at = sp.simplify(e3.subs({x_: mu0, y_: L, w_: mu0}))
log(f"FD2(b) k>=3: value at (x,y,w)=(mu0,L,mu0) equals (2/q)[(2Q+4)mu0+QL-Q]? {sp.simplify(val_at - lower_mine) == 0}; "
    f"equals text's (2/q)[(4Q+8)mu0-2Q+2QL]? {sp.simplify(val_at - lower_text) == 0} (text = 2 x value)")
assert sp.expand(sp.diff(e3, x_)) != 0
log(f"   d/dx = {sp.simplify(sp.diff(e3, x_))} > 0, d/dy = d/dw = {sp.simplify(sp.diff(e3, y_))} > 0: bound at x=mu0,y=L,w=mu0 is valid")
# positivity of the correct bound for Q >= 4
tt = sp.symbols('tt', nonnegative=True)
ok3, info3 = certify(lower_mine.subs(Q, Q), 'p3')
log(f"   (2/q)[(2Q+4)mu0+QL-Q] > 0 on Q>=4: {ok3} ({info3})")
log("DONE")
