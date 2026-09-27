#!/usr/bin/env python3
"""Region search (PROOF.md section 9.16).  For a target NT, enumerate every T(a) that could fail BOTH Row criteria
with N = NT (all usable groups small, k0 small; bounds in section 9.16), compute its exact number N of non-even
secular pairs and N_ei, and report every tree with N >= NT that fails both criteria (a), (b) for its actual N.
Usage: region_search.py NT m r   (shard r of m)."""
import os, sys, itertools
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from row_lemmas import criteria
NT, m, rr = map(int, sys.argv[1:4])
# bounds for failing (a) with N = NT:  beta >= 2: k*beta - 1 - [beta=k=2] <= 2NT ; beta = 1: k1 - 1 <= 2NT
maxb = 2 * NT + 1
kmax = {}
for beta in range(2, maxb + 1):
    k = 0
    while True:
        kk = k + 1
        size = kk * beta - 1 - (1 if (beta == 2 and kk == 2) else 0)
        if size <= 2 * NT: k = kk
        else: break
    kmax[beta] = k
k1max = 2 * NT + 1
betas = sorted(kmax)
count = 0; found = []; idx = 0
for ks in itertools.product(*[range(kmax[b] + 1) for b in betas]):
    if sum(ks) == 0: continue                          # need some branch of size >= 2
    r_big = sum(1 for k in ks if k > 0)
    for k1 in range(0, k1max + 1):
        r_nb = r_big + (1 if k1 > 0 else 0)
        # failing (b) needs 2(k0+1) <= 4NT + N_ei <= 4NT + r  (r <= r_nb + 1)
        k0max = (4 * NT + r_nb + 1) // 2 - 1
        for k0 in range(0, k0max + 1):
            idx += 1
            if (idx - 1) % m != rr: continue
            a = []
            for b, k in zip(betas, ks): a += [b] * k
            a += [1] * k1 + [0] * k0
            a = tuple(sorted(a, reverse=True))
            count += 1
            c = criteria(a)
            if c['N'] >= NT and not c['a'] and not c['b']:
                found.append((a, c['N'], c['Nei'])); print('UNCOVERED', a, 'N=', c['N'], 'Nei=', c['Nei'], flush=True)
print(f"NT={NT} shard={rr}/{m} trees_checked={count} uncovered_with_N>=NT={len(found)}", flush=True)
