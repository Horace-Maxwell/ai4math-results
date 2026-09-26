"""Referee-2, test 10: the facts used in the referee's hand proof that (i) all cells of Y+ vanish and kappa(Y+) = 0, so
G(Y+) = Theta, and (ii) alternation is forced after column b-1, certified symbolically on both regions for a = 2..8
(r2poly certified signs).  Notation: alpha = M s_a, u = M e_a = (p^{a-1}P, ..., P, 1), delta = alpha_a.
  (F1) sgn alpha_i = (-1)^{a-i} (certified);      (F2) |alpha_i| - 2 u_i >= 0 for i < a (== 0 exactly for i = 0);
  (F3) mu0 |alpha_i| - (2/q) u_i >= 0 for i < a    [cells at columns j <= b-2: mu_{b-2-j} >= mu0, q^{-(b-1-j)} <= 1/q];
  (F4) (Q-1) delta - 2 > 0  [i = a, j <= b-2, and j = b-1 for odd a];   delta - 2 > 0  [i = a, j = b-1, even a];
  (F5) (Q-1) delta >= 2 and Q delta - p^a > 0 (last-coordinate forcing; |(M zeta)_a| <= p^a = row sum of the last row);
  (F6) Delta(g_trunc) = 2 delta identically.
"""
import itertools
from r2poly import Region, T_region, padd, ppow

out = open('logs/t10_eq_symbolic.log', 'w')
def log(*a):
    s = ' '.join(str(x) for x in a); print(s); out.write(s + '\n'); out.flush()

for a in range(2, 9):
    for rname in ('big', 'p3'):
        R = Region(rname)
        M = T_region(R, a)
        sa = [(-1) ** i for i in range(a + 1)]
        alpha = [sum((M[i][k] * sa[k] for k in range(a + 1)), R.const(0)) for i in range(a + 1)]
        u = [M[i][a] for i in range(a + 1)]
        Q = R.QQ(); q = Q + 1
        mu0 = (Q - 1).div_q()
        delta = alpha[a]
        for i in range(a + 1):
            assert alpha[i].sign() == (-1) ** (a - i), ('F1', a, rname, i)
        for i in range(a):
            d = alpha[i] * ((-1) ** (a - i)) - u[i] * 2
            assert d.sign() == (0 if i == 0 else 1), ('F2', a, rname, i, d.sign())
            f3 = mu0 * alpha[i] * ((-1) ** (a - i)) - (u[i] * 2).div_q()
            assert all(v >= 0 for v in f3.num.values()), ('F3', a, rname, i)     # >= 0 on the region (= 0 only at i=0, Q=2)
        assert ((Q - 1) * delta - 2).sign() == 1 and (delta - 2).sign() == 1, ('F4', a, rname)
        pa = R.poly(ppow(padd(R.P, {(0, 0): 1}), a))
        assert (Q * delta - pa).sign() == 1, ('F5', a, rname)
        rowlast = sum((M[a][k] for k in range(a + 1)), R.const(0))
        assert (rowlast - pa).sign() == 0, ('last row sum', a, rname)
        # F6
        gt = [((-1) ** a) * x for x in sa]; gt[a] -= 2          # (-1)^b s_a - 2 e_a with b = a mod 2
        Mg = [sum((M[i][k] * gt[k] for k in range(a + 1)), R.const(0)) for i in range(a + 1)]
        D = sum((x.absval() for x in alpha), R.const(0)); Fg = sum((x.absval() for x in Mg), R.const(0))
        assert (D - Fg - delta * 2).sign() == 0, ('F6', a, rname)
    log(f"a={a}: F1-F6 certified on both regions")
