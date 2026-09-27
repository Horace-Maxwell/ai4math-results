#!/usr/bin/env python3
"""Referee stress test of Lemma 9.15.1 (realizability), Lemma 9.15.2/9.15.3 + Lemma 9.22.1 (refined counts),
and Theorem 9.22.2, on trees WITH non-even pairs (found by random search, incl. b* >= 13).

Row members are built from the text of PROOF.md §9.4/§9.15 by the referee's own code:
  base pattern: odd b>=3: lambda=-1 all, but for k_b>=2 the first two get +1,-3; b=1: -1 all, but for k_1>=2 first gets +1;
                even b>=2: 0,-2,0,-2,...;
  leaf row at beta: s_c=eps, sigma=+1 everywhere, base pattern off beta, group beta realises total Lambda (Lemma 9.15.1);
  bare row: s_c=eps, base pattern, sigma=+1 on non-bare, first m bare branches sigma=-1.
Goodness of each member: rank_Fp = d (two primes) => good; otherwise exact Q-rank decides.
Checks: #bad <= 4 N_I + 2 N_II (leaf rows), #bad <= 4 N_I + 2 N_II + N_ei (bare rows); (a')/(b') => some member good;
        b* >= 13 => the b*-row has a good member.
usage: rv_rows.py <seed> <samples> <bmin> <bmax> <nmax>
"""
import sys, random, math
from collections import Counter
import numpy as np
from rv_common import tree_adj, charpoly_tree, distinct_eig_count, krylov_int, rank_Q, P1, P2
from rv_certify import rank_np, krylov_mod
from rv_region import classify, L

def realize(beta, k, Lam):
    """leaf sums lambda_1..lambda_k in {-beta,...,beta} step 2, sum Lam, not all equal (k>=2), some |lambda|<beta.
    Referee's construction: brute force over small cases is too slow in general, so: greedy then repair."""
    M = (k * beta - Lam) // 2          # number of '-' leaves in the group
    assert (k * beta - Lam) % 2 == 0
    assert (0 <= M <= 1) if (beta == 1 and k == 1) else (1 <= M <= k * beta - 1)
    if beta == 1:
        m = [1] * M + [0] * (k - M)
    else:
        q, rem = divmod(M, k)
        m = [q + 1] * rem + [q] * (k - rem)
        if rem == 0 and k >= 2:
            m[0] += 1; m[1] -= 1
    lam = [beta - 2 * x for x in m]
    assert all(0 <= x <= beta for x in m) and sum(lam) == Lam
    if k >= 2: assert len(set(lam)) > 1
    if beta >= 2: assert any(abs(x) < beta for x in lam)
    return lam

def Lset(beta, k):
    if beta == 1:
        return [-1, 1] if k == 1 else list(range(-(k - 2), k - 1, 2))
    out = [x for x in range(-(k * beta - 2), k * beta - 1, 2)]
    if beta == 2 and k == 2: out.remove(0)
    return out

def base_lams(b, k):
    if b == 1:
        return ([1] + [-1] * (k - 1)) if k >= 2 else [-1]
    if b % 2 == 1:
        return ([1, -3] + [-1] * (k - 2)) if k >= 2 else [-1]
    return [0 if j % 2 == 0 else -2 for j in range(k)]

def leaf_signs(b, lam):
    m = (b - lam) // 2
    return [-1] * m + [1] * (b - m)

def build(a, sc, sigma, lams):
    """a in tree_adj order; returns switching vector"""
    k = len(a); s = [sc] + list(sigma)
    for i, ai in enumerate(a):
        s += leaf_signs(ai, lams[i]) if ai > 0 else []
    return s

def goodness(adj, Anp, s, d):
    if rank_np(krylov_mod(Anp, s, d, P1), P1) == d and rank_np(krylov_mod(Anp, s, d, P2), P2) == d:
        return True
    return rank_Q(krylov_int(adj, s, d)) == d

def test_tree(a):
    a = tuple(sorted(a, reverse=True))
    kk = Counter(a); B = sorted(kk); k = len(a)
    import rv_region; rv_region.STRICT = False
    NI, NIIlo, NIIup, Nei, notes = classify(a)
    assert NIIlo == NIIup and all(x[0] == 'irr-by-sympy-only' for x in notes), (a, notes)
    NII = NIIup
    adj = tree_adj(a); n = len(adj); d = distinct_eig_count(charpoly_tree(adj))
    Anp = np.zeros((n, n), dtype=np.int64)
    for i in range(n):
        for u in adj[i]: Anp[i, u] = 1
    idx = {b: [i for i in range(k) if a[i] == b] for b in B}
    base = {}
    for b in B:
        if b >= 1:
            for i, l in zip(idx[b], base_lams(b, kk[b])): base[i] = l
        else:
            for i in idx[b]: base[i] = 0
    report = []
    if max(a) < 2: return None
    for beta in [b for b in B if b >= 1]:
        nbad = 0; ngood = 0
        for eps in (1, -1):
            for Lam in Lset(beta, kk[beta]):
                lams = dict(base)
                for i, l in zip(idx[beta], realize(beta, kk[beta], Lam)): lams[i] = l
                s = build(a, eps, [1] * k, [lams[i] for i in range(k)])
                if goodness(adj, Anp, s, d): ngood += 1
                else: nbad += 1
        bound = 4 * NI + 2 * NII
        crit = len(Lset(beta, kk[beta])) >= 2 * NI + NII + 1
        report.append(('leaf', beta, nbad, ngood, bound, crit))
    if kk.get(0, 0) >= 1:
        nbad = 0; ngood = 0
        for eps in (1, -1):
            for m in range(0, kk[0] + 1):
                sigma = [1] * k
                for j, i in enumerate(idx[0]):
                    if j < m: sigma[i] = -1
                s = build(a, eps, sigma, [base[i] for i in range(k)])
                if goodness(adj, Anp, s, d): ngood += 1
                else: nbad += 1
        bound = 4 * NI + 2 * NII + Nei
        crit = 2 * (kk[0] + 1) > bound
        report.append(('bare', 0, nbad, ngood, bound, crit))
    return a, n, NI, NII, Nei, report

if __name__ == '__main__':
    seed, samples, bmin, bmax, nmax = map(int, sys.argv[1:6])
    rng = random.Random(seed)
    viol = 0; tested = 0; seen = set()
    fixed = [(12, 12, 8) + (0,) * 6, (3, 1, 1, 1, 1, 0, 0, 0), (6, 3, 2) + (0,) * 9, (8, 8, 1, 1, 1, 0, 0),
             (8, 5, 2, 2, 0, 0, 0, 0, 0), (6, 4, 3, 2, 1, 1, 1, 1), (2, 2), (2, 0, 0), (3,)]
    cand = list(fixed)
    for _ in range(samples):
        bstar = rng.randint(bmin, bmax)
        k = rng.randint(1, 9)
        a = [bstar] + [rng.choice([0, 0, 1, 1, 2, 3, 4, rng.randint(0, bstar)]) for _ in range(k - 1)]
        a = tuple(sorted(a, reverse=True))
        if 1 + len(a) + sum(a) > nmax or a in seen: continue
        seen.add(a)
        NI, lo, up, Nei, notes = classify(a)
        if NI + up >= 1: cand.append(a)
    print('candidates with N>=1:', len(cand), flush=True)
    for a in cand:
        r = test_tree(a)
        if r is None: continue
        a, n, NI, NII, Nei, rep = r; tested += 1
        bad_here = False
        for kind, beta, nbad, ngood, bound, crit in rep:
            if nbad > bound or (crit and ngood == 0): bad_here = True
            if kind == 'leaf' and beta == max(a) and max(a) >= 13 and ngood == 0: bad_here = True
        if bad_here: viol += 1
        print('VIOLATION' if bad_here else 'ok', a, 'n=%d N_I=%d N_II=%d N_ei=%d' % (n, NI, NII, Nei),
              ' '.join('%s%d:bad%d/%d(<=%d)%s' % (kind, beta, nbad, nbad + ngood, bound, '*' if crit else '') for kind, beta, nbad, ngood, bound, crit in rep), flush=True)
    print('SUMMARY tested=%d violations=%d' % (tested, viol))
