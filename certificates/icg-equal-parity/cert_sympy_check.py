"""Independent re-implementation (sympy) of the shape-(a,b) certificate, used as a cross-check of cert22.py / cert_fast.py.
T_k(x) is built here from the Ramanujan-sum definition t_ij = phi(x^{k-i}) c_{x^{k-j}}(x^i) (Jiang-Yang (2.2)-(2.4)),
independently of core.T and cert22.Tpoly. The target is computed as G of the anti-checkerboard (symbolically), and the closed form
d_a d_b - 2 delta_a delta_b is checked against it.
"""
import sys, itertools
import sympy as sp
p, q, s, t = sp.symbols('p q s t')

def phi(x, e): return sp.Integer(1) if e == 0 else x ** (e - 1) * (x - 1)
def ram(x, k, i):
    if k == 0: return sp.Integer(1)
    if k <= i: return x ** (k - 1) * (x - 1)
    if k == i + 1: return -x ** (k - 1)
    return sp.Integer(0)
def Tm(k, x): return sp.Matrix(k + 1, k + 1, lambda i, j: phi(x, k - i) * ram(x, k - j, i))

def coeffs_sign(expr):
    P = sp.Poly(sp.expand(expr), s, t)
    cs = P.coeffs() if not P.is_zero else []
    if not cs: return 0, P
    if all(c >= 0 for c in cs): return 1, P
    if all(c <= 0 for c in cs): return -1, P
    return None, P

def run(a, b, p0, q0):
    M = Tm(a, p).subs(p, p0 + s); N = Tm(b, q).subs(q, q0 + t)
    cells = [(i, j) for i in range(a + 1) for j in range(b + 1)]
    corner = (a, b)
    def Zof(Y):
        Ym = sp.Matrix(a + 1, b + 1, lambda i, j: Y[(i, j)])
        return (M * Ym * N.T).applyfunc(sp.expand)
    anti = {(i, j): -(-1) ** (i + j) for (i, j) in cells}
    Za = Zof(anti)
    tgt = sp.expand(sum(sp.Abs(0) for _ in []) + 0)
    # target = G(anti) computed via signs (anti is known to be tight): sum_{c != corner} |Z_c| + Z_corner with |.| by sign test
    tg = 0
    for (u, v) in cells:
        if (u, v) == corner: tg += Za[u, v]; continue
        sg, _ = coeffs_sign(Za[u, v]); assert sg in (1, -1)
        tg += sg * Za[u, v]
    tg = sp.expand(tg)
    def dk(k, x): return (2 * k + 1) * x ** k + 4 * sum((-1) ** (k - j) * (j + 1) * x ** j for j in range(k))
    def delk(k, x): return sp.cancel((x ** k * (x - 1) + 2 * (-1) ** k) / (x + 1))
    closed = sp.expand((dk(a, p) * dk(b, q) - 2 * delk(a, p) * delk(b, q)).subs({p: p0 + s, q: q0 + t}))
    assert sp.expand(tg - closed) == 0, "closed form of the target"
    free = [c for c in cells if c != corner]
    ncert = 0; tight = []; bad = []
    for bits in itertools.product([1, -1], repeat=len(free)):
        Y = dict(zip(free, bits)); Y[corner] = -1
        Z = Zof(Y)
        det = {}; und = []
        for c in cells:
            if c == corner: continue
            sg, _ = coeffs_sign(Z[c])
            if sg is None: und.append(c)
            else: det[c] = sg if sg != 0 else 1
        base = Z[corner] + sum(sg * Z[c] for c, sg in det.items())
        for sb in itertools.product([1, -1], repeat=len(und)):
            val = base + sum(x * Z[c] for c, x in zip(und, sb))
            gap = sp.expand(tg - val)
            if gap == 0:
                tight.append(tuple(Y[c] for c in cells)); continue
            P = sp.Poly(gap, s, t)
            if any(c < 0 for c in P.coeffs()) or P.coeff_monomial(1) <= 0:
                bad.append(tuple(Y[c] for c in cells))
        ncert += 1
    print(f"[sympy] shape ({a},{b}) region p>={p0}, q>={q0}: #Y={ncert} #not-certified={len(bad)} tight={sorted(set(tight))}")

if __name__ == "__main__":
    a, b, p0, q0 = map(int, sys.argv[1:5])
    run(a, b, p0, q0)
