"""Referee-2: plain exhaustive brute force of Conjecture 12 in sign-matrix form, directly from the matrix model
Z = T_a(p) Y T_b(q)^T,  G(Y) = sum_{(i,v) != (a,b)} |Z_iv| + Z_ab,  over ALL Y with Y_ab = -1 (no decomposition, no lemma used).
Exact int64 arithmetic (integer p, q; an explicit bound excludes overflow).  Meet in the middle over columns:
Z = sum_j (M c_j) N[:, j]^T = Z_left + Z_right.
Usage: python3 t7_brute_numpy.py a b p q [workers] [left_cols]
"""
import itertools, sys, time
import numpy as np
from multiprocessing import Pool
from fractions import Fraction as Fr

sys.path.insert(0, '.')
from r2core import T, Theta, G as Gexact, anti, trunc

def setup(a, b, p, q, jl):
    M = np.array([[int(x) for x in row] for row in T(a, p)], dtype=object)
    N = np.array([[int(x) for x in row] for row in T(b, q)], dtype=object)
    bound = max(sum(abs(int(x)) for x in row) for row in M) * max(sum(abs(int(x)) for x in row) for row in N)
    assert bound * (a + 1) * (b + 1) * 4 < 2 ** 62, "overflow risk"
    types = list(itertools.product([1, -1], repeat=a + 1))
    Mt = {t: [sum(int(M[i, k]) * t[k] for k in range(a + 1)) for i in range(a + 1)] for t in types}
    E = (a + 1) * (b + 1)
    V = {}
    for j in range(b + 1):
        for t in types:
            V[(j, t)] = np.array([Mt[t][i] * int(N[v, j]) for i in range(a + 1) for v in range(b + 1)], dtype=np.int64)
    left = list(itertools.product(types, repeat=jl))
    right_types_last = [t for t in types if t[a] == -1]
    right = list(itertools.product(*([types] * (b - jl) + [right_types_last])))
    ZL = np.array([sum((V[(j, c[j])] for j in range(jl)), np.zeros(E, dtype=np.int64)) for c in left], dtype=np.int64)
    ZR = np.array([sum((V[(jl + j, c[j])] for j in range(b + 1 - jl)), np.zeros(E, dtype=np.int64)) for c in right],
                  dtype=np.int64)
    return left, right, ZL, ZR

_G = {}
def init(a, b, p, q, jl, thr):
    left, right, ZL, ZR = setup(a, b, p, q, jl)
    _G.update(dict(a=a, b=b, left=left, right=right, ZL=ZL, ZR=ZR, thr=thr, corner=(a + 1) * (b + 1) - 1))

def work(rng):
    lo, hi = rng
    ZL, ZR, thr, corner = _G['ZL'], _G['ZR'], _G['thr'], _G['corner']
    best = None; hits = []
    for i0 in range(lo, hi, 8):
        i1 = min(hi, i0 + 8)
        Zs = ZL[i0:i1, None, :] + ZR[None, :, :]
        cz = Zs[:, :, corner]
        Gv = np.abs(Zs).sum(axis=2) - np.abs(cz) + cz
        mx = int(Gv.max())
        best = mx if best is None or mx > best else best
        idx = np.argwhere(Gv >= thr)
        for (x, y) in idx:
            hits.append((i0 + int(x), int(y), int(Gv[x, y])))
    return best, hits

if __name__ == "__main__":
    a, b, p, q = map(int, sys.argv[1:5])
    workers = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    jl = int(sys.argv[6]) if len(sys.argv) > 6 else (b + 1) // 2
    t0 = time.time()
    th = Theta(a, b, p, q); thr = int(th)
    left, right, ZL, ZR = setup(a, b, p, q, jl)
    nL = len(left)
    chunks = [(i, min(nL, i + max(64, nL // (workers * 16)))) for i in range(0, nL, max(64, nL // (workers * 16)))]
    best = None; hits = []
    with Pool(workers, initializer=init, initargs=(a, b, p, q, jl, thr)) as pool:
        for bst, h in pool.imap_unordered(work, chunks):
            best = bst if best is None or bst > best else best
            hits.extend(h)
    Ys = []
    for (il, ir, g) in hits:
        cols = list(left[il]) + list(right[ir])
        Y = [[cols[j][i] for j in range(b + 1)] for i in range(a + 1)]
        assert Gexact(Y, T(a, p), T(b, q)) == g
        Ys.append(tuple(map(tuple, Y)))
    ok = best == thr and sorted(Ys) == sorted([tuple(map(tuple, anti(a, b))), tuple(map(tuple, trunc(a, b)))])
    line = (f"brute force ({a},{b}) p={p} q={q}: {len(left) * len(right)} sign matrices; max G = {best}, Theta = {thr}; "
            f"#(G >= Theta) = {len(Ys)}; {'OK: exactly Y-, Y+' if ok else 'MISMATCH'}  [{time.time() - t0:.0f}s]")
    print(line)
    with open('logs/t7_brute_numpy.log', 'a') as f:
        f.write(line + '\n')
