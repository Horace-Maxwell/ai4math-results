"""Implementation 2 (uses only verify_cm.py's parser/product): exhaustive
non-existence checks.

 (1) S_2 and S_3 have no complete mapping (all bijections tried).
 (2) In B_2, B_3, PB_2, PB_3 the rank-n elements are exactly the n! permutation
     diagrams, forming the group of units S_n  (=> no complete mapping of the
     monoid, by Corollary 3.4 of arXiv:2608.25092: a complete mapping of a
     finite monoid restricts to one of its group of units).
 (3) The rank-2 principal factor of PB_3 (18 non-zero elements + 0) has no
     complete mapping: exhaustive depth-first search over all bijections of
     the 19-element factor (zero included, nothing assumed).
 (4) Positive controls: the same search finds complete mappings of the rank-0
     factors of PB_3 and B_4, and of the rank-1 factor of PB_2.
PB_n / B_n elements are enumerated here from itertools.permutations
(involutions of the 2n points), independently of diagrams.py.
"""
import itertools, sys
from verify_cm import mult, rank


def pts(n):
    return [('t', i) for i in range(1, n + 1)] + [('b', i) for i in range(1, n + 1)]


def all_diagrams(n, family):
    P = pts(n)
    out = set()
    for perm in itertools.permutations(range(2 * n)):
        if all(perm[perm[k]] == k for k in range(2 * n)):
            if family == "B" and any(perm[k] == k for k in range(2 * n)):
                continue
            blocks = set()
            for k in range(2 * n):
                blocks.add(frozenset([P[k], P[perm[k]]]))
            out.add(frozenset(blocks))
    return sorted(out, key=lambda d: sorted(tuple(sorted(b)) for b in d))


def is_permutation_diagram(d):
    return all(len(b) == 2 and {p[0] for p in b} == {'t', 'b'} for b in d)


def search_cm(elems, mul):
    """exhaustive DFS for a complete mapping of the finite magma (elems, mul)."""
    m = len(elems)
    table = [[mul(a, b) for b in range(m)] for a in range(m)]
    used_val = [False] * m
    used_prod = [False] * m
    alpha = [None] * m
    nodes = [0]

    def dfs(x):
        nodes[0] += 1
        if x == m:
            return True
        for y in range(m):
            if not used_val[y]:
                z = table[x][y]
                if not used_prod[z]:
                    used_val[y] = used_prod[z] = True
                    alpha[x] = y
                    if dfs(x + 1):
                        return True
                    used_val[y] = used_prod[z] = False
        return False

    ok = dfs(0)
    return ok, (list(alpha) if ok else None), nodes[0]


def factor(n, family, r):
    D = all_diagrams(n, family)
    J = [d for d in D if rank(d) == r]
    elems = J + ['ZERO']
    idx = {e: k for k, e in enumerate(elems)}
    z0 = len(elems) - 1

    def mul(a, b):
        if a == z0 or b == z0:
            return z0
        p = mult(elems[a], elems[b], n)
        return idx[p] if rank(p) == r else z0
    return elems, mul


def group_Sn(n):
    G = list(itertools.permutations(range(n)))
    idx = {g: k for k, g in enumerate(G)}
    return G, (lambda a, b: idx[tuple(G[b][G[a][k]] for k in range(n))])


if __name__ == "__main__":
    for n in (2, 3):
        G, mul = group_Sn(n)
        ok, _, nodes = search_cm(G, mul)
        print(f"S_{n}: complete mapping exists? {ok}  (exhaustive, {nodes} DFS nodes)")
        assert not ok
    for fam in ("B", "PB"):
        for n in (2, 3):
            D = all_diagrams(n, fam)
            top = [d for d in D if rank(d) == n]
            assert len(top) == (2 if n == 2 else 6) and all(is_permutation_diagram(d) for d in top)
            # units: elements u with some v, u v = v u = identity
            ident = frozenset(frozenset([('t', i), ('b', i)]) for i in range(1, n + 1))
            units = [u for u in D if any(mult(u, v, n) == ident and mult(v, u, n) == ident for v in D)]
            assert set(units) == set(top)
            print(f"{fam}_{n}: |monoid|={len(D)}, group of units = the {len(top)} rank-{n} permutation diagrams (S_{n})")
    elems, mul = factor(3, "PB", 2)
    ok, alpha, nodes = search_cm(list(range(len(elems))), mul)
    print(f"PB_3 rank-2 principal factor: {len(elems)} elements (incl. 0); complete mapping exists? {ok}  (exhaustive DFS, {nodes} nodes)")
    assert not ok
    for (n, fam, r) in ((3, "PB", 0), (4, "B", 0), (2, "PB", 1)):
        elems, mul = factor(n, fam, r)
        ok, alpha, nodes = search_cm(list(range(len(elems))), mul)
        print(f"control {fam}_{n} rank-{r} factor ({len(elems)} elements): complete mapping found? {ok} ({nodes} nodes)")
        assert ok
    print("NONEXISTENCE CHECKS PASSED")
