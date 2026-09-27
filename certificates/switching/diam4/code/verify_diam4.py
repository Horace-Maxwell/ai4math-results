#!/usr/bin/env python3
"""Exhaustive exact verification: every tree of diameter <= 4 (= T(a), rooted height <= 2) with 3 <= n <= N
has a good switching.  Certificate: rank_{F_p}[s, As, ..., A^{d-1}s] = d with p = 2^61-1, where d is the number
of distinct eigenvalues from the explicit spectrum lemma (Lemma S in PROOF.md):
   d = 2r + 2*#{b >= 1 : k_b >= 2} + [kernel nonzero],  kernel dim = sum_i (a_i - 1)_{a_i>=1} + (k_0 - 1 if k_0>=1 else 1)
(r = number of distinct values among a_i).  With --check-d, d is ALSO computed independently by sympy
(gcd of charpoly and its derivative) and compared.
Order of candidate switchings: R_A option 1, R_A option 2 (centre flipped), mixed targets, then structured
random search (s_c = +1, random sigma and leaf patterns).  Usage: verify_diam4.py NMIN NMAX m r [--check-d]"""
import os, sys, random
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ht2 import all_ht2, build, make_s
from rules import rule_switch, VARIANTS
from constructions import construction_mixed
P = (1 << 61) - 1

def d_formula(a):
    g = Counter(a); r = len(g)
    d = 2 * r + 2 * sum(1 for b in g if b >= 1 and g[b] >= 2)
    k0 = g.get(0, 0)
    kern = sum(b - 1 for b in a if b >= 1) + ((k0 - 1) if k0 >= 1 else 1)
    return d + (1 if kern > 0 else 0)

def rank_modp(rows):
    M = [list(r) for r in rows]; m = len(M); ncol = len(M[0]); rank = 0
    for col in range(ncol):
        piv = None
        for rr in range(rank, m):
            if M[rr][col]: piv = rr; break
        if piv is None: continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = pow(M[rank][col], P - 2, P)
        for rr in range(rank + 1, m):
            f = M[rr][col]
            if f:
                f = f * inv % P; Mr = M[rr]; Mk = M[rank]
                for c in range(col, ncol): Mr[c] = (Mr[c] - f * Mk[c]) % P
        rank += 1
        if rank == m: break
    return rank

def certified(adj, s, d):
    rows = []; v = [x % P for x in s]
    for _ in range(d):
        rows.append(v); v = [sum(v[w] for w in adj[i]) % P for i in range(len(adj))]
    return rank_modp(rows) == d

def d_sympy(adj):
    import sympy
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'code'))
    from swtrees_A import charpoly
    x = sympy.Symbol('x'); n = len(adj)
    phi = charpoly(adj, n); Pp = sympy.Poly(list(reversed(phi)), x, domain='ZZ')
    return n - sympy.gcd(Pp, Pp.diff(x)).degree()

def candidates(a):
    aa, sg, mu = rule_switch(a, VARIANTS[0]); yield 'RA1', aa, 1, sg, mu
    yield 'RA2', aa, -1, sg, mu
    for S_all in (False, True):
        for mode in ('sigma', 'lambda'):
            aa2, sg2, mu2 = construction_mixed(a, S_all=S_all, b1_mode=mode)
            yield 'MIX', aa2, 1, sg2, mu2
    rng = random.Random(hash(a) & 0xffffffff)
    aa3 = tuple(sorted(a))
    for _ in range(3000):
        sg3 = [rng.choice((1, -1)) for _ in aa3]
        mu3 = [rng.randint(0, b) for b in aa3]
        yield 'RND', aa3, 1, sg3, mu3

if __name__ == '__main__':
    nmin, nmax, m, rr = map(int, sys.argv[1:5]); check_d = '--check-d' in sys.argv
    for n in range(nmin, nmax + 1):
        stats = Counter(); fails = []; dmis = 0; idx = 0; tot = 0
        for a in all_ht2(n):
            idx += 1
            if (idx - 1) % m != rr: continue
            tot += 1
            d = d_formula(a)
            if check_d:
                adj0, _ = build(tuple(sorted(a)))
                if d_sympy(adj0) != d: dmis += 1
            ok = None
            for name, aa, sc, sg, mu in candidates(a):
                s, adj = make_s(aa, sc, sg, mu)
                if certified(adj, s, d): ok = name; break
            if ok: stats[ok] += 1
            else: fails.append(a)
        print(f"n={n} shard={rr}/{m} trees={tot} certified={sum(stats.values())} by_rule={dict(stats)} fail={len(fails)} d_mismatch={dmis if check_d else 'n/a'} {fails[:3]}", flush=True)
