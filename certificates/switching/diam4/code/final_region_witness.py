#!/usr/bin/env python3
"""End-to-end check on the finite region of PROOF.md section 9.22 (implementation 1's enumeration).
For every tree of the region that passes (a') or (b') (cheap test with N_II <= (r - N_rat)//2, or exact N_II),
take the designated family (first beta with (a'), else the bare row), evaluate ALL its members, and check:
  (1) at least one member is good (certified: F_p-rank = d, p = 2^61 - 1);
  (2) the number of members that are not good (uncertified members are re-checked exactly over Q) is at most
      4 N_I + 2 N_II_bound (+ N_ei for the bare row).
Usage: final_region_witness.py m r   (shard)"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import Counter
from ht2 import make_s, is_good
from row_lemmas import L_values, leaf_row_switch, bare_row_switch
from verify_diam4 import certified, d_formula
from final_region import region, int_roots, issq, L_of, exact_pairs
m_, r_ = int(sys.argv[1]), int(sys.argv[2])
st = Counter(); viol = []; maxn = 0
for idx, (B, kk) in enumerate(region()):
    if idx % m_ != r_: continue
    a = tuple(sorted([b for b in B for _ in range(kk[b])], reverse=True))
    n = 1 + len(a) + sum(a); maxn = max(maxn, n)
    r = len(B); rts = int_roots(B, kk)
    NI = sum(1 for v in rts if issq(v)); Nei = sum(1 for v in rts if v % 2 == 0 and not issq(v))
    NIIb = (r - len(rts)) // 2
    fam = None
    for beta in sorted(B, reverse=True):
        if beta >= 1 and L_of(beta, kk[beta]) >= 2 * NI + NIIb + 1: fam = ('leaf', beta); break
    k0 = kk.get(0, 0)
    if fam is None and k0 >= 1 and 2 * (k0 + 1) > 4 * NI + 2 * NIIb + Nei: fam = ('bare', 0)
    if fam is None:
        NI2, NIIb = exact_pairs(B, kk)
        for beta in sorted(B, reverse=True):
            if beta >= 1 and L_of(beta, kk[beta]) >= 2 * NI + NIIb + 1: fam = ('leaf', beta); break
        if fam is None and k0 >= 1 and 2 * (k0 + 1) > 4 * NI + 2 * NIIb + Nei: fam = ('bare', 0)
    if fam is None: st['not covered (listed separately)'] += 1; print('NOTCOVERED', a, n, flush=True); continue
    d = d_formula(a)
    if fam[0] == 'leaf':
        beta = fam[1]; g = Counter(a)
        mem = [leaf_row_switch(a, beta, Lam, eps) for Lam in L_values(beta, g[beta]) for eps in (1, -1)]
        assert len(mem) == 2 * L_of(beta, kk[beta]); bound = 4 * NI + 2 * NIIb
    else:
        mem = [bare_row_switch(a, m, eps) for m in range(k0 + 1) for eps in (1, -1)]; bound = 4 * NI + 2 * NIIb + Nei
    good = bad = 0
    for (aa, sc, sg, mu) in mem:
        s, adj = make_s(aa, sc, sg, mu)
        if certified(adj, s, d): good += 1
        elif is_good(aa, s, adj): good += 1
        else: bad += 1
    st['trees'] += 1; st[fam[0]] += 1; st['members'] += len(mem); st['bad'] += bad
    if good == 0 or bad > bound: viol.append((a, fam, good, bad, bound)); print('VIOLATION', viol[-1], flush=True)
print('WITNESS shard %d/%d' % (r_, m_), dict(st), 'max n', maxn, 'violations', len(viol))
