#!/usr/bin/env python3
"""Implementation A, tier-recording variant: for each tree (canonical-augmentation generator of swtrees_A),
find a small k in {0,1,2,3} such that some s = 1 - 2*1_U with |U| = k is EXACTLY certified good
(sympy gcd for d; Bareiss rank over Q).
Mode 'full' (argv[2] == 'full'): a tier is declared empty only after EVERY member failed the exact test,
  so the reported tier is the exact minimum.
Mode 'fast' (default): only the 3 best members of a tier by floating-point score (> 1e-9) are tested
  exactly, so the reported tier is a certified UPPER bound for the minimum.
Prints, per n, the histogram of tiers; 'none<=3' would mean no certified switching with <= 3 flips.
Usage: python3 swtrees_A_tiers.py NMAX [full|fast]"""
import os, sys, itertools, time, numpy as np, sympy
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from swtrees_A import trees_upto, charpoly, exact_rank, krylov_rows
x = sympy.Symbol('x')
def min_tier(adj, n, full=False):
    phi = charpoly(adj, n); P = sympy.Poly(list(reversed(phi)), x, domain='ZZ')
    d = n - sympy.gcd(P, P.diff(x)).degree()
    A = np.zeros((n, n))
    for i in range(n):
        for j in adj[i]: A[i, j] = 1
    w, V = np.linalg.eigh(A)
    groups = []; cur = [0]
    for i in range(1, n):
        if abs(w[i] - w[cur[-1]]) < 1e-6: cur.append(i)
        else: groups.append(cur); cur = [i]
    groups.append(cur)
    for k in range(4):
        Us = list(itertools.combinations(range(n), k))
        S = np.ones((len(Us), n))
        for r, U in enumerate(Us): S[r, list(U)] = -1
        C = S @ V
        sc = np.min(np.stack([(C[:, g] ** 2).sum(axis=1) for g in groups]), axis=0)
        order = np.argsort(-sc) if full else [r for r in np.argsort(-sc)[:3] if sc[r] > 1e-9]
        for r in order:
            s = [int(t) for t in S[r]]
            if exact_rank(krylov_rows(adj, s, d)) == d:
                return k
    return 'none<=3'
if __name__ == '__main__':
    nmax = int(sys.argv[1]); full = len(sys.argv) > 2 and sys.argv[2] == 'full'; t0 = time.time()
    print('mode', 'full' if full else 'fast', flush=True)
    for n, trees in trees_upto(nmax):
        hist = {}
        for adj in trees:
            k = min_tier(adj, n, full); hist[k] = hist.get(k, 0) + 1
        print(f"n={n} trees={len(trees)} min-tier histogram={dict(sorted(hist.items(), key=str))} time={time.time()-t0:.0f}s", flush=True)
