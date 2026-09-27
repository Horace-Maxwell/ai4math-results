#!/usr/bin/env python3
"""Row Lemmas (PROOF.md section 9.15) for trees T(a) of diameter <= 4.
(a) Leaf-row family for a branch size beta: s_c = eps, sigma = +1 everywhere, all groups at the base pattern of
    construction_I except group beta, whose leaf-sum total Lambda runs over the realizable set L_beta.
(b) Bare-row family: s_c = eps, leaves and non-bare sigma at the base pattern, m bare branches with sigma = -1.
Criteria (crude): (a) |L_beta| >= 2N + 1 for some usable beta;  (b) 2(k0 + 1) > 4N + N_ei.
N = number of non-even secular pairs, N_ei = number of secular roots that are even integers and not squares."""
import os, sys, sympy, math
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from constructions import construction_I
from noneven_census import noneven_pairs, secular_poly
x, t = sympy.symbols('x t')

def L_values(beta, k):
    """realizable leaf-sum totals for the group of size beta with k branches (see Lemma 9.15.1)"""
    if beta >= 2:
        vals = [L for L in range(-k * beta + 2, k * beta - 1, 2)]
        if beta == 2 and k == 2: vals = [L for L in vals if L != 0]
        return vals
    if beta == 1:
        if k >= 2: return list(range(-k + 2, k - 1, 2))
        return [-1, 1]
    return []

def realize(beta, k, Lam):
    """leaf sums lambda_1..lambda_k (each in {-beta,..,beta} step 2) with sum Lam, not all equal if k>=2,
    and (beta>=2) some |lambda_i| < beta.  Returns list of mu_i = number of -1 leaves."""
    if beta == 1:
        M = (k - Lam) // 2                    # number of -1 leaves
        return [1] * M + [0] * (k - M)
    M = (k * beta - Lam) // 2                 # total number of -1 leaves, 1 <= M <= k*beta - 1
    if k == 1: return [M]
    q, rem = divmod(M, k)
    mus = [q + 1] * rem + [q] * (k - rem)
    if rem == 0:                              # all equal: perturb
        mus[0] += 1; mus[1] -= 1
    assert sum(mus) == M and all(0 <= u <= beta for u in mus), (beta, k, Lam, mus)
    lam = [beta - 2 * u for u in mus]
    assert len(set(lam)) > 1 and any(abs(l) < beta for l in lam), (beta, k, Lam, lam)
    return mus

def leaf_row_switch(a, beta, Lam, eps):
    aa, sg, mu = construction_I(a)
    g = Counter(a); k = g[beta]
    new = realize(beta, k, Lam)
    idx = [i for i, b in enumerate(aa) if b == beta]
    mu = list(mu)
    for i, u in zip(idx, new): mu[i] = u
    return aa, eps, [1] * len(aa), mu

def bare_row_switch(a, m, eps):
    aa, sg, mu = construction_I(a)
    sg = [1] * len(aa)
    idx = [i for i, b in enumerate(aa) if b == 0]
    for i in idx[:m]: sg[i] = -1
    return aa, eps, sg, mu

def N_and_Nei(a):
    pairs = noneven_pairs(a)
    R = secular_poly(a)
    Nei = 0
    for rt in sympy.Poly(R, t).ground_roots():       # rational roots of R(t)
        if rt.is_integer and rt % 2 == 0 and math.isqrt(int(rt)) ** 2 != int(rt): Nei += 1
    return len(pairs), Nei, pairs

def criteria(a):
    g = Counter(a); N, Nei, pairs = N_and_Nei(a)
    has_big = any(b >= 2 for b in g)
    res = {'N': N, 'Nei': Nei, 'a': None, 'b': None}
    if not has_big: return res
    for beta in sorted(g, reverse=True):
        if beta == 0: continue
        Ls = L_values(beta, g[beta])
        if len(Ls) >= 2 * N + 1: res['a'] = (beta, len(Ls)); break
    k0 = g.get(0, 0)
    if k0 >= 1 and 2 * (k0 + 1) > 4 * N + Nei: res['b'] = (k0, Nei)
    return res
