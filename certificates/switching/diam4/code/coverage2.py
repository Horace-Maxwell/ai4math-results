# Full classification of trees of diameter <= 4 (T(a), n <= N) by the proven results of PROOF.md section 9:
#   KNOWN (stars, double stars, paths, harmonic trees), E (no non-even secular pair), F (exactly one non-even pair,
#   not the pair x-1, x+1, tree not in the family (1^k1, 0^k0), k0 >= 2), F2 (unique non-even pair is x-1, x+1,
#   and some a_i >= 3), D1 / D1+ / D2 / D3.  Prints the residual (uncovered) trees.
import sys, sympy
from collections import Counter
sys.path.insert(0, '.')
from ht2 import all_ht2
from secular_factors import secular
from theorems_check import classes
x, t = sympy.symbols('x t')
def noneven_factors(a):
    R = secular(a)
    Rx = sympy.Poly(R.as_expr().subs(t, x**2), x)
    out = []
    for f, m in sympy.factor_list(Rx.as_expr())[1]:
        pf = sympy.Poly(f, x); pm = sympy.Poly(f.subs(x, -x), x)
        if not (pm == pf or pm == -pf): out.append(pf)
    return out
def known(a):
    g = Counter(a); nonbare = [b for b in a if b >= 1]
    if len(nonbare) == 0: return 'star'
    if len(nonbare) == 1: return 'double star/star'
    if tuple(sorted(a)) in ((0, 1), (1, 1)): return 'path'
    if len(g) == 1:
        q = a[0] + 1
        if q >= 2 and len(a) == q * q - q + 1: return 'harmonic'
    return None
if __name__ == '__main__':
  N0, N = int(sys.argv[1]), int(sys.argv[2])
  for n in range(N0, N + 1):
      cnt = Counter(); residual = []
      for a in all_ht2(n):
          g = Counter(a)
          ne = noneven_factors(a); npairs = len(ne) // 2
          fam = set(g) <= {0, 1} and g.get(0, 0) >= 2
          labels = []
          if known(a): labels.append('KNOWN')
          if npairs == 0: labels.append('E')
          if npairs == 1:
              pair_is_pm1 = any(f.degree() == 1 and abs(f.all_coeffs()[-1]) == 1 for f in ne)
              if not pair_is_pm1 and not fam: labels.append('F')
              if pair_is_pm1 and any(b >= 3 for b in g) and not fam: labels.append('F2')
          if classes(a): labels.append('D')
          for l in labels: cnt[l] += 1
          if not labels: residual.append((a, [str(f.as_expr()) for f in ne]))
      tot = sum(1 for _ in all_ht2(n))
      print(f"n={n} trees={tot} counts={dict(cnt)} residual={len(residual)} {residual[:6]}", flush=True)
