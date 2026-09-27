# Distribution of the number of non-even secular PAIRS (factor pairs g(x), g(-x)) and their degrees, for T(a), n <= N.
import sys, sympy
from collections import Counter
sys.path.insert(0, '.')
from secular_factors import secular
from ht2 import all_ht2
x, t = sympy.symbols('x t')
N = int(sys.argv[1]); dist = Counter(); examples = {}
degs = Counter()
for n in range(3, N + 1):
    for a in all_ht2(n):
        R = secular(a)
        Rx = sympy.Poly(R.as_expr().subs(t, x**2), x)
        ne = 0
        for f, m in sympy.factor_list(Rx.as_expr())[1]:
            pf = sympy.Poly(f, x); pm = sympy.Poly(f.subs(x, -x), x)
            if not (pm == pf or pm == -pf):
                ne += 1; degs[pf.degree()] += 1
        pairs = ne // 2
        dist[pairs] += 1
        if pairs not in examples or len(examples[pairs]) < 5: examples.setdefault(pairs, []).append(a)
print('number of non-even pairs -> #trees:', dict(sorted(dist.items())))
print('degree distribution of non-even factors:', dict(sorted(degs.items())))
for p in sorted(examples): print(p, examples[p])
