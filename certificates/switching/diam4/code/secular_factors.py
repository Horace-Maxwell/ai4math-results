# For rooted trees of height <= 2, T(a): centre c, children v_1..v_k, v_i has a_i leaves.
# Secular polynomial R(t) = prod_b (t-b) - sum_b k_b prod_{b'!=b} (t-b')  (b over DISTINCT a-values, k_b multiplicities).
# Factor R(x^2) over Q; report non-even factors (g(-x) != +-g(x)).
import sys, itertools, sympy
from collections import Counter
x, t = sympy.symbols('x t')
def partitions_multiset(total_leaves, k, maxpart):
    # nonincreasing sequences of length k with parts in [0, maxpart] summing to total_leaves
    if k == 0:
        if total_leaves == 0: yield ()
        return
    for first in range(min(maxpart, total_leaves), -1, -1):
        for rest in partitions_multiset(total_leaves - first, k - 1, first):
            yield (first,) + rest
def secular(a):
    cnt = Counter(a); bs = sorted(cnt)
    R = sympy.Integer(1)
    for b in bs: R *= (t - b)
    S = 0
    for b in bs:
        term = sympy.Integer(cnt[b])
        for b2 in bs:
            if b2 != b: term *= (t - b2)
        S += term
    return sympy.Poly(sympy.expand(R - S), t)
N = int(sys.argv[1])
noneven = []
total = 0
for n in range(3, N + 1):
    for k in range(1, n):
        L = n - 1 - k
        if L < 0: continue
        for a in partitions_multiset(L, k, L):
            total += 1
            R = secular(a)
            Rx = sympy.Poly(R.as_expr().subs(t, x**2), x)
            for f, m in sympy.factor_list(Rx.as_expr())[1]:
                pf = sympy.Poly(f, x)
                pm = sympy.Poly(f.subs(x, -x), x)
                if not (pm == pf or pm == -pf):
                    noneven.append((n, a, str(f)))
print('trees T(a) enumerated (n<=%d):' % N, total)
print('non-even secular factors:', len(noneven))
from collections import defaultdict
byf = defaultdict(list)
for n, a, f in noneven: byf[f].append(a)
for f, lst in sorted(byf.items(), key=lambda z: (len(z[0]), z[0])):
    print(f, ' count', len(lst), ' e.g.', lst[:4])
