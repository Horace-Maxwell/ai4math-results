# For a given T(a) and switching s: list irreducible factors p of the minimal polynomial with (mu/p)(A)s == 0
# (exact integer arithmetic) -> the non-main eigenvalue orbits.
import sys, sympy
sys.path.insert(0, '.')
from ht2 import build, make_s
x = sympy.Symbol('x')
def bad_factors(a, s):
    adj, _ = build(a); n = len(adj)
    A = sympy.zeros(n, n)
    for i in range(n):
        for j in adj[i]: A[i, j] = 1
    facs = [sympy.Poly(f, x) for f, m in sympy.factor_list(A.charpoly(x).as_expr())[1]]
    mu = sympy.Poly(1, x)
    for f in facs: mu = mu * f
    bad = []
    for f in facs:
        q = sympy.Poly(sympy.quo(mu.as_expr(), f.as_expr(), x), x).all_coeffs()
        v = [0] * n
        for c in q: v = [sum(v[w] for w in adj[i]) + int(c) * s[i] for i in range(n)]
        if all(z == 0 for z in v): bad.append(str(f.as_expr()))
    return bad
if __name__ == '__main__':
    from rules import rule_switch, VARIANTS
    from ht2 import all_ht2, is_good
    N = int(sys.argv[1]); vi = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    for n in range(3, N + 1):
        for a in all_ht2(n):
            aa, sigma, mu = rule_switch(a, VARIANTS[vi])
            s, adj = make_s(aa, 1, sigma, mu)
            if not is_good(aa, s, adj):
                print(n, a, 'bad factors:', bad_factors(aa, s), flush=True)
