#!/usr/bin/env python3
"""Consistency check of the refined Row Lemma counts (PROOF.md section 9.22, Lemma 9.22.1).
For every tree T(a) with NMIN <= n <= NMAX and max a_i >= 2:
  * for EVERY beta >= 1 in B, the leaf-row family {s_(eps,Lambda)} has at most 4 N_I + 2 N_II bad members;
  * if k0 >= 1, the bare-row family {s_(eps,m)} has at most 4 N_I + 2 N_II + N_ei bad members.
A member counts as good only if certified: rank over F_p (p = 2^61 - 1) of [s, As, ..., A^(d-1)s] equals d
(d from Lemma S).  So the bad counts are upper bounds, and any violation is re-checked exactly (Bareiss over Q).
Usage: test_refined_rows.py NMIN NMAX [m r]   (shard: trees with index % m == r)"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import Counter
from ht2 import all_ht2, make_s, is_good
from row_lemmas import L_values, leaf_row_switch, bare_row_switch
from verify_diam4 import certified, d_formula
from final_region import int_roots, issq, exact_pairs

N0, N1 = int(sys.argv[1]), int(sys.argv[2])
m_, r_ = (int(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (1, 0)
viol = []; st = Counter(); idx = 0
def count_bad(members, a, d):
    bad = 0; badlist = []
    for (aa, sc, sg, mu) in members:
        s, adj = make_s(aa, sc, sg, mu)
        if not certified(adj, s, d):
            if not is_good(aa, s, adj): bad += 1          # exact re-check of every uncertified member
    return bad
for n in range(N0, N1 + 1):
    for a in all_ht2(n):
        g = Counter(a)
        if max(g) < 2: continue
        idx += 1
        if idx % m_ != r_: continue
        B = sorted(g); kk = dict(g)
        rts = int_roots(B, kk)
        NI, NII = exact_pairs(B, kk)
        Nei = sum(1 for v in rts if v % 2 == 0 and not issq(v))
        d = d_formula(a)
        st['trees'] += 1; st['N_I>0'] += NI > 0; st['N_II>0'] += NII > 0
        for beta in B:
            if beta == 0: continue
            mem = [leaf_row_switch(a, beta, Lam, eps) for Lam in L_values(beta, g[beta]) for eps in (1, -1)]
            bad = count_bad(mem, a, d)
            st['leaf-rows'] += 1; st['leaf-members'] += len(mem); st['leaf-bad'] += bad
            if bad > 4 * NI + 2 * NII: viol.append(('leaf', a, beta, bad, NI, NII))
        k0 = g.get(0, 0)
        if k0 >= 1:
            mem = [bare_row_switch(a, m, eps) for m in range(k0 + 1) for eps in (1, -1)]
            bad = count_bad(mem, a, d)
            st['bare-rows'] += 1; st['bare-members'] += len(mem); st['bare-bad'] += bad
            if bad > 4 * NI + 2 * NII + Nei: viol.append(('bare', a, bad, NI, NII, Nei))
    print(f"n<={n} shard {r_}/{m_}: {dict(st)} violations={len(viol)} {viol[-3:]}", flush=True)
print('DONE shard', r_, m_, 'violations', len(viol))
for v in viol: print('VIOLATION', v)
