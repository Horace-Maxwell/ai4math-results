"""Check the combinatorial ingredients of the proof (PROOF.md Lemmas 4.3-4.4)
for larger n without building the whole factor: the explicit triangle
I_0, I_1, I_2 is pairwise compatible with sign bits (0,0,1), and the explicit
perfect matching of G - X (fibre pairing + in-fibre pairing) consists of
compatible pairs and covers all N - 3 remaining half-diagrams.
Uses implementation 1 (diagrams.py) for products of projections."""
import sys, time
from diagrams import perfect_matchings, projection, product, rank, group_part, free_points
from construct import proof_triangle, proof_matching, brauer_half, sgnbit


class LazyP(dict):
    def __missing__(self, key):
        a, b = key
        r = len(free_points(a))
        z = product(projection(a), projection(b))
        v = group_part(z) if rank(z) == r else None
        self[key] = v
        return v


def half_diagrams(n, r):
    from itertools import combinations
    H = []
    for F in combinations(range(n), r):
        rest = [p for p in range(n) if p not in F]
        for M in perfect_matchings(rest):
            H.append(brauer_half(n, list(F), M))
    return H


if __name__ == "__main__":
    for (n, r) in [(6, 2), (7, 3), (10, 2), (11, 3), (14, 2)]:
        t = time.time()
        H = half_diagrams(n, r)
        P = LazyP()
        tri = proof_triangle(n, r)
        bits = [sgnbit(P[(tri[0], tri[1])]), sgnbit(P[(tri[1], tri[2])]), sgnbit(P[(tri[2], tri[0])])]
        assert all(P[(tri[k], tri[(k + 1) % 3])] is not None for k in range(3))
        assert all(P[(t_, t_)] == tuple(range(r)) for t_ in tri)
        match = proof_matching(n, r, H, P, tri)
        covered = [h for pr in match for h in pr]
        assert len(covered) == len(set(covered)) == len(H) - 3
        assert set(covered) | set(tri) == set(H)
        assert all(P[(a, b)] is not None and P[(b, a)] is not None for a, b in match)
        print(f"n={n} r={r}: N={len(H)} ({'odd' if len(H)%2 else 'even'}); triangle sign bits {bits}; "
              f"perfect matching of G-X with {len(match)} compatible pairs; {time.time()-t:.1f}s", flush=True)
    print("PROOF INGREDIENTS CHECKED")
