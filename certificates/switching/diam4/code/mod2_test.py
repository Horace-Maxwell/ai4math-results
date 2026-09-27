# Test: for each non-even secular factor g of T(a) (root theta, t = theta^2), is the norm of
# H_1(theta) = E(t) + sum_b k_b (theta + b) E_b(t)   [= E(t) * (1 . x_theta), x_c = 1]
# odd? If yes, then for EVERY switching s, s . x_theta != 0 (mod-2 argument).
import sys, sympy
from collections import Counter
sys.path.insert(0, '.')
from secular_factors import partitions_multiset, secular
x, t = sympy.symbols('x t')
def H1(a):
    cnt = Counter(a); bs = sorted(cnt)
    E = sympy.Integer(1)
    for b in bs: E *= (x**2 - b)
    H = E
    for b in bs:
        Eb = sympy.Integer(1)
        for b2 in bs:
            if b2 != b: Eb *= (x**2 - b2)
        H += cnt[b] * (x + b) * Eb
    return sympy.Poly(sympy.expand(H), x)
N = int(sys.argv[1])
odd = even = 0; bad = []
for n in range(3, N + 1):
    for k in range(1, n):
        L = n - 1 - k
        for a in partitions_multiset(L, k, L):
            R = secular(a)
            Rx = sympy.Poly(R.as_expr().subs(t, x**2), x)
            H = H1(a)
            for f, m in sympy.factor_list(Rx.as_expr())[1]:
                pf = sympy.Poly(f, x); pm = sympy.Poly(f.subs(x, -x), x)
                if pm == pf or pm == -pf: continue
                res = sympy.resultant(pf, H, x)
                if res % 2: odd += 1
                else: even += 1; bad.append((a, str(f), int(res)))
print('non-even orbits: norm odd', odd, ' norm even', even)
for z in bad[:30]: print('  EVEN', z)
