"""Structural checks with implementation 1 (diagrams.py).

(1) |B_n| = (2n-1)!!, |PB_n| = number of involutions of [2n].
(2) For small n: Green's D (= J, finite) classes are exactly the rank classes
    (computed from principal right and left ideals).
(3) Rees coordinates: for every rank r, x -> (U(x), g(x), L(x)) is a bijection
    onto H_r x S_r x H_r, and for all x, y of rank r:
      rank(xy) = r  <=>  P[L(x),U(y)] defined, and then
      (U(xy), g(xy), L(xy)) = (U(x), g(x) P[L(x),U(y)] g(y), L(y)).
(4) P is reflexive with identity diagonal and symmetric in support, with
    P[i,l] = P[l,i]^{-1}.
"""
import sys, math
from collections import Counter
from diagrams import *


def dfact(k):
    return 1 if k <= 0 else k * dfact(k - 2)


def involutions(k):
    a = [1, 1]
    for j in range(2, k + 1):
        a.append(a[-1] + (j - 1) * a[-2])
    return a[k]


def green_D_classes(S):
    idx = {x: t for t, x in enumerate(S)}
    Sset = S
    right = [frozenset([x] + [product(x, s) for s in Sset]) for x in S]
    left = [frozenset([x] + [product(s, x) for s in Sset]) for x in S]
    # R-class key: right ideal; L-class key: left ideal
    Rkey = {x: right[t] for t, x in enumerate(S)}
    Lkey = {x: left[t] for t, x in enumerate(S)}
    # D = R o L : x D y iff exists z with x R z and z L y.
    Rcls = {}
    for x in S:
        Rcls.setdefault(Rkey[x], []).append(x)
    Lcls = {}
    for x in S:
        Lcls.setdefault(Lkey[x], []).append(x)
    # union-find over R and L classes
    parent = {x: x for x in S}

    def f(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for cls in list(Rcls.values()) + list(Lcls.values()):
        for z in cls[1:]:
            ra, rb = f(cls[0]), f(z)
            if ra != rb:
                parent[ra] = rb
    D = {}
    for x in S:
        D.setdefault(f(x), []).append(x)
    return list(D.values())


def check_rees(S, n, label):
    ranks = sorted({rank(x) for x in S})
    out = []
    for r in ranks:
        J = [x for x in S if rank(x) == r]
        H = halves(S, r)
        Hl = sorted({lower_half(x) for x in J}, key=repr)
        assert H == Hl, "upper/lower half sets differ"
        P = sandwich(H)
        # bijection
        coords = {(upper_half(x), group_part(x), lower_half(x)) for x in J}
        assert len(coords) == len(J) == len(H) ** 2 * math.factorial(r), (label, r)
        for (U, g, L) in coords:
            assert assemble(U, g, L) in set(J)
        # reflexive / symmetric
        for a in H:
            assert P[(a, a)] == tuple(range(r))
            for b in H:
                if P[(a, b)] is None:
                    assert P[(b, a)] is None
                else:
                    assert P[(b, a)] == inverse(P[(a, b)])
        # multiplication (all pairs, or a large sample if too big)
        pairs = len(J) ** 2
        if pairs <= 4_000_000:
            it = ((x, y) for x in J for y in J)
        else:
            import random
            rnd = random.Random(1)
            it = ((rnd.choice(J), rnd.choice(J)) for _ in range(400000))
        cnt = 0
        for x, y in it:
            z = product(x, y)
            p = P[(lower_half(x), upper_half(y))]
            if rank(z) == r:
                assert p is not None
                assert upper_half(z) == upper_half(x) and lower_half(z) == lower_half(y)
                assert group_part(z) == compose(compose(group_part(x), p), group_part(y))
            else:
                assert p is None and rank(z) < r
            cnt += 1
        deg = Counter(sum(1 for b in H if P[(a, b)] is not None) for a in H)
        out.append((r, len(H), len(J), cnt, dict(deg)))
    return out


if __name__ == "__main__":
    for n in range(1, 7):
        B = brauer_elements(n)
        assert len(B) == dfact(2 * n - 1)
        print(f"B_{n}: |B|={len(B)}", flush=True)
        if n <= 5:
            D = green_D_classes(B)
            byrank = sorted((sorted({rank(x) for x in c}), len(c)) for c in D)
            assert all(len(rs) == 1 for rs, _ in byrank)
            assert len(D) == len({rank(x) for x in B})
            print(f"  D-classes = rank classes: {byrank}", flush=True)
        for row in check_rees(B, n, f"B_{n}"):
            r, N, sizeJ, cnt, deg = row
            print(f"  rank {r}: N={N} ({'odd' if N % 2 else 'even'}), |J|={sizeJ}, products checked={cnt}, support degree distribution={deg}", flush=True)
    for n in range(1, 6):
        PB = partial_brauer_elements(n)
        assert len(PB) == involutions(2 * n)
        print(f"PB_{n}: |PB|={len(PB)}", flush=True)
        if n <= 4:
            D = green_D_classes(PB)
            byrank = sorted((sorted({rank(x) for x in c}), len(c)) for c in D)
            assert all(len(rs) == 1 for rs, _ in byrank)
            assert len(D) == len({rank(x) for x in PB})
            print(f"  D-classes = rank classes: {byrank}", flush=True)
        for row in check_rees(PB, n, f"PB_{n}"):
            r, N, sizeJ, cnt, deg = row
            print(f"  rank {r}: N={N} ({'odd' if N % 2 else 'even'}), |J|={sizeJ}, products checked={cnt}, support degree distribution={deg}", flush=True)
    print("ALL STRUCTURE CHECKS PASSED")
