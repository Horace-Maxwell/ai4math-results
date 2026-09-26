"""Exhaustive scan of G(Y) over sign matrices with Y_ab=-1 (float64, Kronecker form), for real p,q.
Reports max G vs target, number of maximisers, and the smallest positive relative margins.
Usage: python3 scan_real.py
"""
import numpy as np, itertools, sys
from fractions import Fraction as Fr
from core import T, target, dfun, delta_last


def run(a, b, p, q, top=6):
    M = np.array([[float(v) for v in r] for r in T(a, p)])
    N = np.array([[float(v) for v in r] for r in T(b, q)])
    K = np.kron(M, N)  # vec_rowmajor(Z) = K vec_rowmajor(Y)
    nc = (a + 1) * (b + 1)
    corner = nc - 1
    tgt = float(target(a, b, p, q))
    best = []
    free = nc - 1
    B = 1 << free
    chunk = 1 << min(free, 16)
    vals_all = []
    for start in range(0, B, chunk):
        idx = np.arange(start, min(B, start + chunk), dtype=np.int64)
        Yf = ((idx[:, None] >> np.arange(free)) & 1) * 2 - 1
        Y = np.concatenate([Yf, -np.ones((len(idx), 1), dtype=np.int64)], axis=1)
        Z = Y @ K.T
        G = np.abs(Z).sum(1) - np.abs(Z[:, corner]) + Z[:, corner]
        order = np.argsort(-G)[:top]
        for o in order:
            best.append((G[o], int(idx[o])))
        best.sort(reverse=True)
        best = best[:top]
    return tgt, best


def fmt(mask, a, b):
    nc = (a + 1) * (b + 1)
    bits = [((mask >> t) & 1) * 2 - 1 for t in range(nc - 1)] + [-1]
    rows = []
    for i in range(a + 1):
        rows.append(''.join('+' if bits[i * (b + 1) + j] > 0 else '-' for j in range(b + 1)))
    return '/'.join(rows)


if __name__ == "__main__":
    shapes = [(1, 1), (2, 2), (1, 3), (3, 1), (3, 3), (2, 4), (4, 2), (1, 5), (5, 1)]
    pairs = [(5, 3), (3, 5), (5, 5), (3, 3), (Fr(9, 2), 3), (4, 3), (5, Fr(5, 2)), (7, 3), (11, 3), (5, 7), (13, 11), (40, 3), (5, 40), (100, 100)]
    for (a, b) in shapes:
        for (p, q) in pairs:
            if (a + 1) * (b + 1) > 16:
                continue
            tgt, best = run(a, b, p, q)
            top = best[0][0]
            nmax = sum(1 for g, m in best if abs(g - top) <= 1e-9 * max(1, abs(top)))
            ok = top <= tgt * (1 + 1e-12) + 1e-9
            second = [g for g, m in best if g < top - 1e-9 * max(1, abs(top))]
            gap = (tgt - second[0]) / tgt if second else float('nan')
            print(f"a={a} b={b} p={float(p):g} q={float(q):g}: max={top:.6f} target={tgt:.6f} {'OK' if ok else 'FAIL'} "
                  f"ties={nmax} relgap_next={gap:.4g} argmax={[fmt(m, a, b) for g, m in best[:nmax]]}")
        sys.stdout.flush()
