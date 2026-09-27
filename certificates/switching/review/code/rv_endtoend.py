#!/usr/bin/env python3
"""Referee end-to-end test of the case logic of Theorem 9.22 on ALL T(a) with b* >= 2 and n in a range:
  exact (N_I, N_II, N_ei) [rv_region.classify, certified]; full leaf rows at every beta and the bare row
  [rv_rows.test_tree, exact goodness]; checks
   (1) bad counts within 4N_I+2N_II (leaf) / 4N_I+2N_II+N_ei (bare),
   (2) (a') at beta => row beta has a good member; (b') => bare row has a good member,
   (3) every tree satisfies (a') or (b') except T(2,2), T(2,0,0), T(3),
   (4) b* >= 13 => (a') holds at beta = b* and row b* has a good member.
usage: rv_endtoend.py <nmin> <nmax> <nproc>        or   rv_endtoend.py big <nmax> <nproc>  (only b* >= 13, only row b*)
"""
import sys
from multiprocessing import Pool
from rv_certify import multisets_upto
from rv_rows import test_tree

EXC = {(2, 2), (2, 0, 0), (3,)}

def work(a):
    r = test_tree(a)
    if r is None: return None
    a, n, NI, NII, Nei, rep = r
    issues = []
    anycrit = False
    for kind, beta, nbad, ngood, bound, crit in rep:
        if nbad > bound: issues.append('count>%s' % kind)
        if crit:
            anycrit = True
            if ngood == 0: issues.append('crit-but-no-good:%s%d' % (kind, beta))
    if not anycrit and a not in EXC: issues.append('no-criterion')
    if max(a) >= 13:
        rb = [x for x in rep if x[0] == 'leaf' and x[1] == max(a)][0]
        if not rb[5] or rb[3] == 0: issues.append('thm9.22.2')
    return a, n, NI, NII, Nei, issues

if __name__ == '__main__':
    if sys.argv[1] == 'big':
        nmax = int(sys.argv[2]); nproc = int(sys.argv[3])
        trees = [a for a in multisets_upto(nmax) if a and max(a) >= 13]
    else:
        nmin, nmax, nproc = map(int, sys.argv[1:4])
        trees = [a for a in multisets_upto(nmax) if a and max(a) >= 2 and 1 + len(a) + sum(a) >= nmin]
    print('trees', len(trees), flush=True)
    bad = 0; tested = 0; from collections import Counter; Nd = Counter()
    with Pool(nproc) as pool:
        for res in pool.imap_unordered(work, trees, chunksize=10):
            if res is None: continue
            a, n, NI, NII, Nei, issues = res; tested += 1; Nd[(NI, NII)] += 1
            if issues: bad += 1; print('ISSUE', a, n, NI, NII, Nei, issues, flush=True)
    print('N_I,N_II distribution:', dict(sorted(Nd.items())))
    print('SUMMARY tested=%d trees-with-issues=%d' % (tested, bad))
