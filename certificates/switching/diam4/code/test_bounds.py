#!/usr/bin/env python3
"""Sanity check of the counting bounds used in Theorem 9.22.2 and Lemma 9.22.3 (PROOF.md section 9.22),
with exact N_I, N_II (factorisation of R(x^2) over Q) for every tree T(a) with NMIN <= n <= NMAX, b* >= 2:
  (1) N_I <= sq + 1, sq = #{q >= 1 : q^2 <= b* - 1, q^2 not a branch size};
  (2) N_I + 2 N_II + N_ei <= r = number of distinct branch sizes;
  (3) if b* >= 13: criterion (a') holds at beta = b*, i.e. |L_{b*}| >= 2 N_I + N_II + 1;
  (4) the tree is covered: b* >= 13, or (a') for some beta, or (b'), or it is one of T(2,2), T(2,0,0), T(3).
Usage: test_bounds.py NMIN NMAX m r"""
import os, sys, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import Counter
from ht2 import all_ht2
from final_region import int_roots, issq, exact_pairs, L_of
N0, N1, m_, r_ = map(int, sys.argv[1:5])
st = Counter(); viol = []; idx = 0
LEFT = {(2, 2), (2, 0, 0), (3,)}
for n in range(N0, N1 + 1):
    for a in all_ht2(n):
        g = Counter(a); bs = max(a)
        if bs < 2: continue
        idx += 1
        if idx % m_ != r_: continue
        B = sorted(g); kk = dict(g); r = len(B)
        rts = int_roots(B, kk); NI, NII = exact_pairs(B, kk)
        assert NI == sum(1 for v in rts if issq(v))
        Nei = sum(1 for v in rts if v % 2 == 0 and not issq(v))
        sq = sum(1 for q in range(1, math.isqrt(bs - 1) + 1) if q * q not in g)
        st['trees'] += 1; st['N>=2'] += (NI + NII) >= 2; st['N>=3'] += (NI + NII) >= 3
        if NI > sq + 1: viol.append(('NI', a, NI, sq))
        if NI + 2 * NII + Nei > r: viol.append(('roots', a, NI, NII, Nei, r))
        if bs >= 13:
            st['b*>=13'] += 1
            if L_of(bs, g[bs]) < 2 * NI + NII + 1: viol.append(('thmH', a))
        k0 = g.get(0, 0)
        oka = any(L_of(b, g[b]) >= 2 * NI + NII + 1 for b in B if b >= 1)
        okb = k0 >= 1 and 2 * (k0 + 1) > 4 * NI + 2 * NII + Nei
        if not (bs >= 13 or oka or okb or a in LEFT): viol.append(('uncovered', a))
        if not (oka or okb): st['fails a/b'] += 1
    print(f"n<={n} shard {r_}/{m_}: {dict(st)} violations={len(viol)} {viol[-3:]}", flush=True)
print('DONE', r_, m_, 'violations', len(viol))
