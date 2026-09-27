#!/usr/bin/env python3
"""Referee: find and certify a good switching for every tree in a list, independently of Lemmas S/M/rows.

usage: rv_certify.py region <listfile> <nproc>          trees from rv_region_list.txt
       rv_certify.py upto <nmax> <nproc>                all T(a) (multisets) with 3 <= n <= nmax
Certificate: d = deg phi - deg gcd(phi, phi') with phi from the generic tree recursion (exact);
             s good iff rank [s, As, ..., A^{d-1}s] = d; certified by rank over F_p = d for two primes
             (rank_Fp <= rank_Q <= d), and, when n <= EXACT_N, also by exact Q-rank.
Search: random switchings (seeded per tree), up to 400 tries.  Also cross-checks d against the Lemma S formula.
"""
import sys, random
from collections import Counter
from multiprocessing import Pool
import numpy as np
from rv_common import tree_adj, charpoly_tree, distinct_eig_count, krylov_int, rank_Q, P1, P2

EXACT_N = 40

def lemmaS_d(a):
    kk = Counter(a); B = sorted(kk); k0 = kk.get(0, 0)
    m0 = (sum(x - 1 for x in a if x >= 1) + k0 - 1) if k0 >= 1 else 1 + sum(x - 1 for x in a)
    return 2 * len(B) + 2 * sum(1 for b in B if b >= 1 and kk[b] >= 2) + (1 if m0 > 0 else 0)

def rank_np(M, p):
    M = M.copy() % p
    d, n = M.shape; rank = 0
    for col in range(n):
        if rank == d: break
        nz = np.nonzero(M[rank:, col])[0]
        if nz.size == 0: continue
        piv = rank + nz[0]
        if piv != rank: M[[rank, piv]] = M[[piv, rank]]
        inv = pow(int(M[rank, col]), p - 2, p)
        M[rank] = (M[rank] * inv) % p
        f = M[:, col].copy(); f[rank] = 0
        M = (M - np.outer(f, M[rank]) % p) % p
        rank += 1
    return rank

def krylov_mod(Anp, s, d, p):
    K = np.zeros((d, len(s)), dtype=np.int64)
    v = np.array(s, dtype=np.int64) % p
    for j in range(d):
        K[j] = v
        v = (Anp @ v) % p
    return K

def work(a):
    a = tuple(a)
    adj = tree_adj(a); n = len(adj)
    phi = charpoly_tree(adj)
    d = distinct_eig_count(phi)
    dS = lemmaS_d(a)
    Anp = np.zeros((n, n), dtype=np.int64)
    for i in range(n):
        for u in adj[i]: Anp[i, u] = 1
    rng = random.Random(hash(a) & 0xffffffff)
    for tries in range(1, 401):
        s = [rng.choice((1, -1)) for _ in range(n)]
        if rank_np(krylov_mod(Anp, s, d, P1), P1) == d and rank_np(krylov_mod(Anp, s, d, P2), P2) == d:
            exact = None
            if n <= EXACT_N:
                exact = (rank_Q(krylov_int(adj, s, d)) == d)
            return (a, n, d, dS, tries, ''.join('+' if x > 0 else '-' for x in s), exact)
    return (a, n, d, dS, None, None, None)

def multisets_upto(nmax):
    """all multisets a (nonincreasing tuples) with 3 <= 1 + len(a) + sum(a) <= nmax"""
    out = []
    def rec(prefix, maxpart, used):
        n = 1 + len(prefix) + sum(prefix)
        if n >= 3: out.append(tuple(prefix))
        for x in range(min(maxpart, nmax - n - 1), -1, -1):
            if n + 1 + x <= nmax:
                rec(prefix + [x], x, used)
    rec([], nmax, 0)
    return out

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'region':
        trees = [tuple(int(x) for x in l.split()) for l in open(sys.argv[2]) if l.strip()]
        nproc = int(sys.argv[3])
    else:
        trees = multisets_upto(int(sys.argv[2])); nproc = int(sys.argv[3])
    print('trees', len(trees), flush=True)
    nfail = 0; dmis = 0; exact_bad = 0; nexact = 0; maxtries = 0
    with Pool(nproc) as pool:
        for res in pool.imap_unordered(work, trees, chunksize=20):
            a, n, d, dS, tries, s, exact = res
            if d != dS: dmis += 1; print('D-MISMATCH', a, d, dS)
            if tries is None: nfail += 1; print('NO-CERT', a, n, d, flush=True)
            else:
                maxtries = max(maxtries, tries)
                if exact is not None:
                    nexact += 1
                    if not exact: exact_bad += 1; print('EXACT-DISAGREE', a, s)
    print('SUMMARY trees=%d uncertified=%d d-mismatch(LemmaS)=%d exactQ-checked=%d exactQ-disagree=%d max-random-tries=%d'
          % (len(trees), nfail, dmis, nexact, exact_bad, maxtries))
