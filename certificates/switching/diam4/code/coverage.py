# Coverage of the proven classes: (E) all secular factors even  OR  D1 / D1+ / D2 / D3.
# Also verifies the Theorem-E switching on class E trees exactly (sigma = +1, s_c = +1, leaf patterns of construction_I,
# bare-leaf sigma flip for a = (1^k1, 0^k0) with k0 >= 2).
import sys, sympy
from collections import Counter
sys.path.insert(0, '.')
from ht2 import all_ht2, make_s, is_good
from secular_factors import secular
from theorems_check import classes
from constructions import construction_I
x, t = sympy.symbols('x t')
def all_even(a):
    R = secular(a)
    Rx = sympy.Poly(R.as_expr().subs(t, x**2), x)
    for f, m in sympy.factor_list(Rx.as_expr())[1]:
        pf = sympy.Poly(f, x); pm = sympy.Poly(f.subs(x, -x), x)
        if not (pm == pf or pm == -pf): return False
    return True
def switch_E(a):
    aa, sg, mu = construction_I(a)
    g = Counter(a)
    if set(g) <= {0, 1} and g.get(0, 0) >= 2:
        sg = list(sg); sg[0] = -1            # aa is nondecreasing, so index 0 is a bare branch
    return aa, sg, mu
N0, N = int(sys.argv[1]), int(sys.argv[2])
for n in range(N0, N + 1):
    tot = cE = cD = cU = 0; bad = []; unc = []
    for a in all_ht2(n):
        tot += 1
        e = all_even(a); d = bool(classes(a))
        if e:
            cE += 1
            aa, sg, mu = switch_E(a); s, adj = make_s(aa, 1, sg, mu)
            if not is_good(aa, s, adj): bad.append(a)
        if d: cD += 1
        if e or d: cU += 1
        else: unc.append(a)
    print(f"n={n} trees={tot} classE={cE} classD={cD} union={cU} ({100*cU/tot:.2f}%) uncovered={tot-cU} E-switch failures={bad[:5]} uncovered_examples={unc[:6]}", flush=True)
