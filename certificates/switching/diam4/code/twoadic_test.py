# 2-adic test: for each non-even secular factor g (root theta) of T(a), is H1(theta)/2 an algebraic integer,
# where H1 = E(t)*G_1(theta) = E(t) + sum_b k_b (theta + b) E_b(t)  (s = all-ones)?
# If NOT, then theta is main for EVERY switching (since E*G_s == E*G_1 mod 2 O_K).
import sys, sympy
from collections import Counter
sys.path.insert(0, '.')
from ht2 import all_ht2
from noneven_census import noneven_pairs
x, y, X = sympy.symbols('x y X')
def H1poly(a):
    g = Counter(a); bs = sorted(g)
    E = sympy.Integer(1)
    for b in bs: E *= (x**2 - b)
    H = E
    for b in bs:
        Eb = sympy.Integer(1)
        for b2 in bs:
            if b2 != b: Eb *= (x**2 - b2)
        H += g[b] * (x + b) * Eb
    return sympy.Poly(sympy.expand(H), x)
def charpoly_of(gpoly, hpoly):
    # characteristic polynomial of h(theta) over Q, theta root of irreducible monic g: Res_y(g(y), X - h(y))
    return sympy.Poly(sympy.resultant(gpoly.as_expr().subs(x, y), X - hpoly.as_expr().subs(x, y), y), X)
N = int(sys.argv[1]); free = 0; notfree = 0; examples = []
for n in range(3, N + 1):
    for a in all_ht2(n):
        pairs = noneven_pairs(a)
        if not pairs: continue
        H = H1poly(a)
        for g in pairs:
            for gg in (g, sympy.Poly(g.as_expr().subs(x, -x), x)):
                gg = gg.monic()
                cp = charpoly_of(gg, sympy.Poly(H.as_expr() / 2, x))
                integral = all(c.is_integer for c in cp.monic().all_coeffs())
                if integral: notfree += 1
                else: free += 1; examples.append((a, str(gg.as_expr())))
print('orbits where H1/2 is NOT integral (main for every switching):', free, ' integral:', notfree)
print('examples free:', examples[:10])
