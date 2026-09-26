#!/usr/bin/env python3
"""Validate the exact test of sunD (test mode) against exact multiplicities.

For random generalized sun graphs (b = 3..12, mixed P1/P2, n <= 60) the exact multiplicity of
every integer k in [-9, 9] is computed as the nullity of A - kI over Q (fraction-free Bareiss
elimination in Python integers, on the full n x n adjacency matrix: no structure used).
sunD's nu_k must be >= mult(k) (soundness) and, for a good prime, equal to it.
Also checks: sum_k mult(k) = n  <=>  integral  (numpy eigenvalues as a third opinion).
Usage: validate_D.py SUND_BINARY NGRAPHS SEED
"""
import random, subprocess, sys
import numpy as np

def adjacency(b, p, q):
    n = b + sum(p) + 2 * sum(q)
    A = [[0] * n for _ in range(n)]
    def e(u, v):
        A[u][v] = A[v][u] = 1
    for k in range(b):
        e(k, (k + 1) % b)
    nxt = b
    for k in range(b):
        for _ in range(p[k]):
            e(k, nxt); nxt += 1
        for _ in range(q[k]):
            e(k, nxt); e(nxt, nxt + 1); nxt += 2
    assert nxt == n
    return A

def rank_Q(M):
    M = [row[:] for row in M]
    n, m = len(M), len(M[0])
    r, prev = 0, 1
    for c in range(m):
        piv = next((i for i in range(r, n) if M[i][c] != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(r + 1, n):
            for j in range(c + 1, m):
                M[i][j] = (M[i][j] * M[r][c] - M[i][c] * M[r][j]) // prev
            M[i][c] = 0
        prev = M[r][c]
        r += 1
        if r == n:
            break
    return r

def main():
    binary, ng, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    graphs = []
    known = [(4, [6, 0, 3, 0], [0, 0, 0, 0]), (4, [0, 1, 0, 1], [5, 0, 2, 0]), (4, [0] * 4, [4, 4, 0, 0]),
             (6, [0, 6, 6, 12, 6, 6], [0] * 6), (4, [0] * 4, [10, 10, 0, 0]), (6, [0] * 6, [0] * 6)]
    graphs += known
    while len(graphs) < ng:
        b = rng.randint(3, 12)
        style = rng.random()
        p = [0] * b; q = [0] * b
        for k in range(b):
            if rng.random() < 0.6:
                p[k] = rng.choice([0, 1, 1, 2, 3, rng.randint(0, 12)])
            if rng.random() < 0.4:
                q[k] = rng.choice([0, 1, 1, 2, rng.randint(0, 6)])
        if style < 0.3:   # impose a rotation / reflection symmetry to get repeated eigenvalues
            d = rng.choice([x for x in range(1, b + 1) if b % x == 0])
            p = [p[k % d] for k in range(b)]; q = [q[k % d] for k in range(b)]
        elif style < 0.45:
            p = [p[min(k, (b - k) % b)] for k in range(b)]; q = [q[min(k, (b - k) % b)] for k in range(b)]
        n = b + sum(p) + 2 * sum(q)
        if n > 60:
            continue
        graphs.append((b, p, q))
    inp = "".join(f"{b} " + " ".join(f"{p[k]} {q[k]}" for k in range(b)) + "\n" for b, p, q in graphs)
    out = subprocess.run([binary, "test"], input=inp, capture_output=True, text=True, check=True).stdout.split("\n")
    bad = unsound = 0; nint = 0; stats = {"mult2": 0, "zero_heavy": 0}
    for (b, p, q), line in zip(graphs, out):
        vals = list(map(int, line.split()))
        n, nu = vals[0], vals[1:]
        A = adjacency(b, p, q)
        assert len(A) == n
        mult = []
        for k in range(-9, 10):
            M = [[A[i][j] - (k if i == j else 0) for j in range(n)] for i in range(n)]
            mult.append(n - rank_Q(M))
        ev = np.linalg.eigvalsh(np.array(A, dtype=float))
        num = [int(np.sum(np.abs(ev - k) < 1e-6)) for k in range(-9, 10)]
        if any(nu[i] < mult[i] for i in range(19)):
            unsound += 1; print("UNSOUND", b, p, q, nu, mult)
        if nu != mult or mult != num:
            bad += 1; print("MISMATCH", b, p, q, "nu", nu, "exact", mult, "numpy", num)
        if sum(mult) == n:
            nint += 1
        stats["mult2"] += sum(1 for i in range(19) if abs(i - 9) >= 2 and mult[i] == 2)
        stats["zero_heavy"] += (mult[9] > 0)
    print(f"graphs={len(graphs)} unsound={unsound} mismatches={bad} integral={nint} "
          f"eigs|k|>=2 with mult 2: {stats['mult2']}  graphs with mult(0)>0: {stats['zero_heavy']}")

if __name__ == "__main__":
    main()
