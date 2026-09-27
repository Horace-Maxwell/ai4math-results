#!/usr/bin/env python3
"""Referee: the b* <= 1 part of Theorem 9.22 (all a_i <= 1).

(1) Family A = T(1^{k1}, 0^{k0}), k0,k1 >= 2, switching of §9.7 (s_c=+, one bare leaf -, sigma=+ on P2-branches,
    one far leaf -).  Referee's own derivation: G = P + theta*Q with P=(t+k1-3)/(t-1), Q=(t-2)/t at a secular t;
    the secular polynomial h(t) = t^2 - (1+k0+k1) t + k0 has no integer root (roots in (0,1) and (k0+k1, k0+k1+1)),
    hence is irreducible; a failure needs P^2 = t Q^2, i.e. f(t) = t(t+k1-3)^2 - (t-2)^2 (t-1)^2 = 0, i.e. h | f.
    We compute the remainder f mod h = c1*t + c0 in Z[k0,k1] and solve c1 = c0 = 0 exactly.
(2) T(1, 0^{k0}), k0 >= 2: failure iff R has root 2 or R = t^2 - 3t + 1  (derived by hand in the review).
(3) Direct Krylov certificates of the stated switchings for families over ranges (sanity), and of s+/s- for
    T(1^{k1}, 0) (k0 = 1, Main Theorem) and s+ for spiders T(1^{k1}) (class D1).
"""
import sympy
from rv_common import tree_adj, charpoly_tree, distinct_eig_count, krylov_int, rank_Q
from rv_certify import rank_np, krylov_mod
import numpy as np
from rv_common import P1, P2

t, k0, k1 = sympy.symbols('t k0 k1')
h = t**2 - (1 + k0 + k1) * t + k0
f = t * (t + k1 - 3)**2 - (t - 2)**2 * (t - 1)**2
rem = sympy.Poly(sympy.rem(sympy.expand(f), h, t), t)
c1 = sympy.expand(rem.coeff_monomial(t)); c0 = sympy.expand(rem.coeff_monomial(1))
print('f mod h = (c1) t + (c0) with')
print('  c1 =', sympy.factor(c1)); print('  c0 =', sympy.factor(c0))
res = sympy.factor(sympy.resultant(c1, c0, k0))
print('  Res_k0(c1, c0) =', res)
# integer solutions with k0, k1 >= 2
sols = []
for fac, e in sympy.factor_list(sympy.resultant(c1, c0, k0))[1]:
    for r in sympy.Poly(fac, k1).all_roots() if sympy.Poly(fac, k1).degree() > 0 else []:
        if r.is_integer and r >= 2:
            for r0 in sympy.Poly(c1.subs(k1, r), k0).all_roots():
                if r0.is_integer and r0 >= 2 and sympy.expand(c0.subs({k1: r, k0: r0})) == 0:
                    sols.append((int(r0), int(r)))
print('  integer solutions (k0, k1) >= 2 of c1 = c0 = 0:', sols)
# also: is c1 = c0 = 0 possibly a common curve?  check gcd
print('  gcd(c1, c0) =', sympy.gcd(c1, c0))

# (2) T(1, 0^k0): R(t) = t^2 - (k0+2) t + k0
R2 = t**2 - (k0 + 2) * t + k0
print('T(1,0^k0): R(2) =', sympy.expand(R2.subs(t, 2)), '; R == t^2-3t+1 iff k0+2 = 3 and k0 = 1 -> k0 = 1 only')
# symbolic re-derivation of G for T(1,0^k0) with the stated switching
th = sympy.Symbol('th')
G = 1 + ((k0 - 2) * th) / th**2 + (th - 1) / (th**2 - 1)   # s_c + sum over bare (sigma*th)/t + (th + lambda)/(t-1)
# use F=1: k0/t = 1 - 1/(t-1)
print('  G numerator:', sympy.factor(sympy.together(G.subs(k0, (th**2 - 2) * th**2 / (th**2 - 1)))))

def cert(a, s):
    adj = tree_adj(a); n = len(adj); d = distinct_eig_count(charpoly_tree(adj))
    Anp = np.zeros((n, n), dtype=np.int64)
    for i in range(n):
        for u in adj[i]: Anp[i, u] = 1
    return rank_np(krylov_mod(Anp, s, d, P1), P1) == d and rank_np(krylov_mod(Anp, s, d, P2), P2) == d

bad = []
# family A and T(1,0^k0): tree_adj order: a = (1,)*k1 + (0,)*k0 -> centre, k1 P2-branch vertices, k0 bare vertices, k1 far leaves
for K1 in range(1, 41):
    for K0 in range(2, 41):
        a = (1,) * K1 + (0,) * K0
        n = 1 + K1 + K0 + K1
        s = [1] * n
        s[1 + K1] = -1                 # one bare leaf -
        s[1 + K1 + K0] = -1            # one far leaf -
        if not cert(a, s): bad.append(('famA/T(1,0^k0)', K1, K0))
# stars T(0^k0): one bare leaf -, (two for k0 = 4)
for K0 in range(2, 81):
    a = (0,) * K0; s = [1] * (1 + K0); s[1] = -1
    if K0 == 4: s[2] = -1
    if not cert(a, s): bad.append(('star', K0))
# spiders T(1^k1): s+ (sigma=+, far leaves: first +, others -), and T(1^k1, 0): s+ or s-
for K1 in range(1, 81):
    a = (1,) * K1; n = 1 + 2 * K1
    s = [1] * n
    for j in range(1, K1): s[1 + K1 + j] = -1
    if K1 == 1: s[2] = -1          # base pattern: lambda = -1 when k1 = 1
    if not cert(a, s): bad.append(('spider s+', K1))
    a2 = (1,) * K1 + (0,); n2 = n + 1
    sp = [1] * n2
    for j in range(1, K1): sp[1 + K1 + 1 + j] = -1
    if K1 == 1: sp[3] = -1         # base pattern: lambda = -1 when k1 = 1
    sm = list(sp); sm[0] = -1
    gp, gm = cert(a2, sp), cert(a2, sm)
    if not (gp or gm): bad.append(('T(1^k1,0) s+/s-', K1))
print('direct certificates: family A / T(1,0^k0) for k1<=40, 2<=k0<=40; stars k0<=80; spiders and T(1^k1,0) k1<=80; failures:', bad)

sext = k1**6 - 11*k1**5 + 60*k1**4 - 148*k1**3 + 224*k1**2 - 192*k1 + 64
print('sextic integer roots among divisors of 64:', [v for v in range(-64, 65) if v != 0 and 64 % abs(v) == 0 and sext.subs(k1, v) == 0])
