#!/usr/bin/env python3
"""Session 3, PROOF.md section 9.22 (implementation 1): the finite remainder of the complete theorem.

Refined Row criteria (Lemma 9.22.1), for a tree T(a) with b* = max a_i >= 2:
  (a') some beta >= 1 in B with |L_beta| >= 2*N_I + N_II + 1;
  (b') k0 >= 1 and 2*(k0 + 1) > 4*N_I + 2*N_II + N_ei.
N_I  = number of secular roots t that are perfect squares (integer non-even pairs),
N_II = number of non-even pairs whose t has degree >= 2,
N_ei = number of secular roots that are even non-square integers.
Theorem 9.22.2: (a') holds at beta = b* whenever b* >= 13.  Lemma 9.22.3 gives a-priori bounds for a tree with
2 <= b* <= 12 that fails (a') for every beta and (b'); this script enumerates that finite set (pruned per group
set B), computes N_I, N_ei and the number N_rat of integer secular roots exactly, bounds N_II <= (r - N_rat)//2,
and prints every tree that still fails.  For those it computes the exact N_II by factoring R(x^2) over Q.
Usage: final_region.py            (prints REGION/SURVIVOR/EXACT lines and a summary)"""
import sys, math
from itertools import product
import sympy
X = sympy.Symbol('x')

def L_of(beta, k):
    """|L_beta| of Lemma 9.15.1"""
    if beta == 1: return 2 if k == 1 else k - 1
    return k * beta - 1 - (1 if (beta == 2 and k == 2) else 0)

def issq(v): return v >= 0 and math.isqrt(v) ** 2 == v

def R_at(t, B, kk):
    """R(t) = prod(t-b) - sum_b k_b prod_{b' != b}(t-b'), exact integers"""
    tot = 1
    for b in B: tot *= (t - b)
    s = 0
    for b in B:
        p = kk[b]
        for b2 in B:
            if b2 != b: p *= (t - b2)
        s += p
    return tot - s

def int_roots(B, kk):
    """all integer secular roots: integers strictly between consecutive poles, and in (b*, b* + K]"""
    K = sum(kk.values()); c = []
    for j in range(len(B) - 1): c += range(B[j] + 1, B[j + 1])
    c += range(B[-1] + 1, B[-1] + K + 1)
    return [t for t in c if R_at(t, B, kk) == 0]

def region():
    for bs in range(2, 13):
        S = math.isqrt(bs - 1)
        for mask in range(1 << bs):
            B = [b for b in range(bs) if mask >> b & 1] + [bs]
            r = len(B)
            sqm = sum(1 for q in range(1, S + 1) if q * q not in B)
            NImax = min(sqm + 1, r)
            T = 2 * NImax + (r - NImax) // 2            # max of 2 N_I + N_II
            if L_of(bs, 1) > T: continue
            ch = []
            for b in B:
                if b == 0: ch.append(list(range(1, (3 * NImax + r) // 2)))   # 2(k0+1) <= 3 N_I + r
                else: ch.append([k for k in range(1, 4 * T + 5) if L_of(b, k) <= T])
            for ks in product(*ch):
                yield B, dict(zip(B, ks))

def exact_pairs(B, kk):
    """exact (N_I, N_II) by factoring R(x^2) over Q"""
    R = sympy.expand(sympy.prod([X**2 - b for b in B]) -
                     sum(kk[b] * sympy.prod([X**2 - c for c in B if c != b]) for b in B))
    NI = NII2 = 0
    for f, m in sympy.factor_list(R)[1]:
        p = sympy.Poly(f, X)
        q = sympy.Poly(f.subs(X, -X), X)
        if p == q or p == -q: continue                  # even factor
        if p.degree() == 1: NI += 1
        else: NII2 += 1
    assert NI % 2 == 0 and NII2 % 2 == 0
    return NI // 2, NII2 // 2

if __name__ == '__main__':
    ntree = 0; surv = []
    for B, kk in region():
        ntree += 1
        r = len(B); rts = int_roots(B, kk)
        NI = sum(1 for v in rts if issq(v))
        Nei = sum(1 for v in rts if v % 2 == 0 and not issq(v))
        NIIup = (r - len(rts)) // 2
        k0 = kk.get(0, 0)
        oka = any(L_of(b, kk[b]) >= 2 * NI + NIIup + 1 for b in B if b >= 1)
        okb = k0 >= 1 and 2 * (k0 + 1) > 4 * NI + 2 * NIIup + Nei
        if not (oka or okb): surv.append((B, kk, NI, Nei, rts))
    print('REGION trees enumerated:', ntree)
    print('SURVIVORS of the cheap test (N_II bounded by (r - N_rat)//2):', len(surv))
    final = []
    for B, kk, NI, Nei, rts in surv:
        a = tuple(sorted([b for b in B for _ in range(kk[b])], reverse=True))
        NI2, NII = exact_pairs(B, kk)
        assert NI2 == NI
        k0 = kk.get(0, 0)
        oka = any(L_of(b, kk[b]) >= 2 * NI + NII + 1 for b in B if b >= 1)
        okb = k0 >= 1 and 2 * (k0 + 1) > 4 * NI + 2 * NII + Nei
        n = 1 + len(a) + sum(a)
        print('SURVIVOR', a, 'n=%d' % n, 'N_I=%d N_II=%d N_ei=%d' % (NI, NII, Nei), 'int_roots=%s' % rts,
              'covered_by_exact' if (oka or okb) else 'FAILS')
        if not (oka or okb): final.append((a, n, NI, NII, Nei))
    print('FINAL trees failing (a\') and (b\') with exact counts:', len(final))
    for f in final: print('FINAL', f)
