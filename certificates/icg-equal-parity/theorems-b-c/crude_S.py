"""Crude Lemma S for F-side T_a(p), path prime q = 3 (Q = 2): s >= chat*Delta(c) - (2 mu/q) sum_i (max_i - Q|A_i|)^+,
max_i = max over sign vectors of |(T_a c)_i|.  Affine in mu -> check mu in {mu_0 = 1/3, 1}; p = 5..60 and p = 101, 1001."""
import itertools
from fractions import Fraction as Fr
from core import T, dfun
def crude(a, p, q=3):
    p = Fr(p); q = Fr(q); Q = q - 1
    M = T(a, p); Dp = dfun(a, p)
    cols = list(itertools.product([1, -1], repeat=a + 1))
    Av = {c: [sum(M[i][k] * c[k] for k in range(a + 1)) for i in range(a + 1)] for c in cols}
    mx = [max(abs(Av[c][i]) for c in cols) for i in range(a + 1)]
    worst = None
    for c in cols:
        for mu in (Fr(1, 3), Fr(1)):
            chat = Q * (1 + mu) / q
            lb = chat * (Dp - sum(abs(x) for x in Av[c])) - (2 * mu / q) * sum(max(0, mx[i] - Q * abs(Av[c][i])) for i in range(a + 1))
            if worst is None or lb < worst[0]: worst = (lb, c, mu)
    return worst
for a in [2, 3, 4, 5]:
    bad = [(p, crude(a, p)) for p in list(range(5, 61, 2)) + [101, 1001] if crude(a, p)[0] < 0]
    print(f"a={a}: crude Lemma S (q=3) fails for {len(bad)} values of p; first failures: {[(p, float(w[0]), w[1], str(w[2])) for p, w in bad[:4]]}")
