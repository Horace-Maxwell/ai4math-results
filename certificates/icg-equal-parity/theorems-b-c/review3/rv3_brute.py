"""Referee-3 plain exhaustive search (no lemma used): all sign matrices Y of shape (a+1) x (b+1) with y_ab = -1 at integer
(p, q); G(Y) = sum_{(i,j) != (a,b)} |Z_ij| + Z_ab with Z = T_a(p) Y T_b(q)^T, in int64 (an overflow bound is asserted).

Z = sum_j (M c_j) n_j^T with n_j the column j of N = T_b(q); the search is vectorised over the last two columns and keeps,
streaming, the TOP largest distinct values of G with their multiplicities and the list of maximisers.
Usage: python3 rv3_brute.py a,b@p,q ... [--cmp]
With --cmp the branch and bound of rv3_bnb.py is run with the largest and the TOP-th largest value as thresholds and the
numbers of matrices found are compared.
"""
import itertools, sys, time
import numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from rv3_bnb import T, dk, bnb, extremal

TOP = 6


def brute(a, b, p, q):
    M = [[int(z) for z in row] for row in T(a, p)]
    N = [[int(z) for z in row] for row in T(b, q)]
    vecs = list(itertools.product([1, -1], repeat=a + 1))
    nv = len(vecs)
    Mc = np.array([[sum(M[i][k] * c[k] for k in range(a + 1)) for i in range(a + 1)] for c in vecs], dtype=np.int64)
    Nn = np.array(N, dtype=np.int64)
    bound = (a + 1) * (b + 1) * int(np.abs(Mc).max()) * int(np.abs(Nn).max()) * (b + 1)
    assert bound < 2 ** 62, 'int64 overflow risk'
    U = [np.einsum('ci,v->civ', Mc, Nn[:, j]).reshape(nv, -1) for j in range(b + 1)]
    idx_last = [k for k, c in enumerate(vecs) if c[a] == -1]
    corner = a * (b + 1) + b
    pair = (U[b - 1][:, None, :] + U[b][None, idx_last, :]).reshape(-1, U[0].shape[1])
    nl = len(idx_last)
    counts = {}
    maxv, maxlist = None, []
    total = 0
    for pre in itertools.product(range(nv), repeat=b - 1):
        base = np.zeros(U[0].shape[1], dtype=np.int64)
        for j, ci in enumerate(pre):
            base = base + U[j][ci]
        Z = pair + base
        G = np.abs(Z).sum(axis=1) - np.abs(Z[:, corner]) + Z[:, corner]
        total += len(G)
        cut = sorted(counts)[-TOP] if len(counts) >= TOP else None
        sel = G if cut is None else G[G >= cut]
        if len(sel):
            u, cn = np.unique(sel, return_counts=True)
            for v, n in zip(u.tolist(), cn.tolist()):
                counts[v] = counts.get(v, 0) + n
            for v in sorted(counts)[:-TOP]:
                del counts[v]
        gm = int(G.max())
        if maxv is None or gm > maxv:
            maxv, maxlist = gm, []
        if gm == maxv:
            for k in np.nonzero(G == gm)[0].tolist():
                cols = [vecs[ci] for ci in pre] + [vecs[k // nl], vecs[idx_last[k % nl]]]
                maxlist.append([[cols[j][i] for j in range(b + 1)] for i in range(a + 1)])
    return total, maxv, maxlist, counts


def run(a, b, p, q, cmp_=False):
    t0 = time.time()
    total, mx, maxY, counts = brute(a, b, p, q)
    Da, dela = dk(a, p)
    Db, delb = dk(b, q)
    Th = int(Da * Db - 2 * dela * delb)
    Ym, Yp = extremal(a, b)
    ok = (mx == Th) and sorted(map(str, maxY)) == sorted(map(str, [Ym, Yp]))
    top = sorted(counts, reverse=True)
    msg = (f'brute ({a},{b}) p={p} q={q}: {total} sign matrices; max G = {mx}, Theta = {Th}; #max = {len(maxY)}; '
           f'{"OK: exactly Y-, Y+" if ok else "UNEXPECTED"}; top values (value:count) '
           f'{[(v, counts[v]) for v in top]}')
    if cmp_:
        for kth in (1, len(top)):
            thr = top[kth - 1]
            nb = sum(counts[v] for v in top[:kth])
            _, res, nodes = bnb(a, b, p, q, threshold=Fr(thr))
            same = (len(res) == nb) and all(g >= thr for g, _ in res)
            msg += f' | B&B at the {kth}-th value: {len(res)} matrices vs brute {nb}: {"agree" if same else "DISAGREE"} ({nodes} nodes)'
            ok = ok and same
    print(msg + f'  [{time.time() - t0:.1f}s]', flush=True)
    return ok


if __name__ == '__main__':
    cmp_ = '--cmp' in sys.argv
    runs = [x for x in sys.argv[1:] if '@' in x]
    nf = 0
    for r in runs:
        sh, pt = r.split('@')
        a_, b_ = map(int, sh.split(','))
        p_, q_ = map(int, pt.split(','))
        nf += not run(a_, b_, p_, q_, cmp_=cmp_)
    print(f'runs {len(runs)}, failures {nf}')
