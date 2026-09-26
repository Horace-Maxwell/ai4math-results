"""Item 8/9 supplement: sanity search for larger even b (beyond exhaustive reach), exact int64 arithmetic.
 (1) every Y within Hamming distance <= 2 of Y- or Y+ (corner fixed at -1): G < Theta strictly (except Y-, Y+ themselves);
 (2) the whole rank-one family Y = g y^T (g in {+-1}^3, y in {+-1}^{b+1}, corner -1) exhaustively for b <= 16:
     max G <= Theta, equality only at Y-, and the best non-extremal gap (the paper's tight families live here);
 (3) 300 random restarts of greedy single-flip ascent: never exceeds Theta; any Theta-attaining endpoint is Y- or Y+.
"""
import sys, itertools, time
import numpy as np
from fractions import Fraction as Fr
from rv_common import T, Theta, Yminus, Yplus

rng = np.random.default_rng(2026)
out = []
def log(s):
    print(s); sys.stdout.flush(); out.append(s)


def mats(b, p, q):
    M = np.array([[int(v) for v in r] for r in T(2, p)], dtype=np.int64)
    N = np.array([[int(v) for v in r] for r in T(b, q)], dtype=np.int64)
    bound = int(np.abs(M).sum(axis=1).max()) * int(np.abs(N).sum(axis=1).max()) * 3 * (b + 1)
    assert bound < 2 ** 62
    return M, N


def Gbatch(Ys, M, N):
    Z = np.einsum('ik,nkl,jl->nij', M, Ys, N)
    return np.abs(Z).sum(axis=(1, 2)) - np.abs(Z[:, 2, -1]) + Z[:, 2, -1]


for (b, pairs) in [(10, [(5, 3), (3, 5), (7, 3), (3, 7), (101, 3)]), (12, [(5, 3), (3, 5), (11, 3)]),
                   (16, [(5, 3), (3, 5), (7, 3)]), (20, [(5, 3), (3, 5), (101, 3)])]:
    for (p, q) in pairs:
        t0 = time.time()
        M, N = mats(b, p, q)
        Th = Theta(2, b, p, q); assert Th.denominator == 1; Th = int(Th)
        Ym = np.array(Yminus(2, b), dtype=np.int64); Yp = np.array(Yplus(2, b), dtype=np.int64)
        cells = [(i, j) for i in range(3) for j in range(b + 1) if (i, j) != (2, b)]
        # (1) Hamming <= 2
        worst1 = None
        for base in (Ym, Yp):
            batch = []
            for r in (1, 2):
                for comb in itertools.combinations(cells, r):
                    Y = base.copy()
                    for (i, j) in comb:
                        Y[i, j] = -Y[i, j]
                    batch.append(Y)
            Gs = Gbatch(np.array(batch), M, N)
            ok_idx = [k for k in range(len(batch)) if not ((batch[k] == Ym).all() or (batch[k] == Yp).all())]
            g = Gs[ok_idx]
            assert (g < Th).all(), ("Hamming search found G >= Theta", b, p, q)
            worst1 = min(worst1, int(Th - g.max())) if worst1 is not None else int(Th - g.max())
        # (2) rank one
        msg2 = ''
        if b <= 16:
            ys = np.array(list(itertools.product((1, -1), repeat=b + 1)), dtype=np.int64)
            best_nonext = None
            for g in itertools.product((1, -1), repeat=3):
                g = np.array(g, dtype=np.int64)
                sel = ys[g[2] * ys[:, -1] == -1]
                Mg = M @ g                      # Z = (Mg)(Ny)^T
                Ny = sel @ N.T
                Z = Mg[None, :, None] * Ny[:, None, :]
                Gv = np.abs(Z).sum(axis=(1, 2)) - np.abs(Z[:, 2, -1]) + Z[:, 2, -1]
                assert (Gv <= Th).all()
                Ys = g[None, :, None] * sel[:, None, :]
                is_ext = ((Ys == Ym).all(axis=(1, 2))) | ((Ys == Yp).all(axis=(1, 2)))
                assert (Gv[Gv == Th] == Th).all() and is_ext[Gv == Th].all()
                ne = Gv[~is_ext]
                if len(ne):
                    v = int(Th - ne.max())
                    best_nonext = v if best_nonext is None else min(best_nonext, v)
            msg2 = f"rank-one family exhaustive: max <= Theta, smallest non-extremal gap {best_nonext}; "
        # (3) greedy ascent
        best_found = None; hits = 0
        for rst in range(300):
            Y = rng.choice(np.array([1, -1]), size=(3, b + 1)); Y[2, b] = -1
            cur = int(Gbatch(Y[None], M, N)[0])
            improved = True
            while improved:
                improved = False
                cand = []
                for (i, j) in cells:
                    Y2 = Y.copy(); Y2[i, j] = -Y2[i, j]; cand.append(Y2)
                Gs = Gbatch(np.array(cand), M, N)
                k = int(np.argmax(Gs))
                if Gs[k] > cur:
                    Y = cand[k]; cur = int(Gs[k]); improved = True
            assert cur <= Th
            if cur == Th:
                assert (Y == Ym).all() or (Y == Yp).all()
                hits += 1
            best_found = cur if best_found is None else max(best_found, cur)
        log(f"(2,{b}) p={p} q={q}: Hamming<=2 around Y-,Y+: all G < Theta (smallest gap {worst1}); {msg2}"
            f"greedy ascent x300: max found {best_found} vs Theta {Th} (reached Theta {hits} times, always at Y-/Y+) "
            f"({time.time() - t0:.1f}s)")
log("DONE")
