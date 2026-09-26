"""Referee-2: validate the branch-and-bound (bnb.py) against plain brute force (matrix model) on small shapes.

For each (a,b,p,q): brute force computes G(Y) for every Y with Y_ab = -1 (r2core.G, exact), sorts the distinct values, and takes
thresholds  Theta  and  the 5th / 12th largest distinct value.  B&B with the same threshold must return exactly the same set of
matrices.  This checks that the B&B bound never prunes a matrix with G >= threshold (including thresholds below Theta,
i.e. non-maximisers), and that the maximum is Theta with exactly the two conjectured maximisers.
"""
import itertools, sys, time
from fractions import Fraction as Fr
from r2core import T, G, Theta, anti, trunc
from bnb import bnb

out = open('logs/t5_bnb_validate.log', 'w')
def log(*a):
    s = ' '.join(str(x) for x in a); print(s); out.write(s + '\n'); out.flush()

cases = [(2, 2, 5, 3), (2, 2, 3, 5), (2, 2, 7, 3), (1, 3, 5, 3), (3, 1, 3, 5), (1, 1, 5, 3), (3, 3, 5, 3), (3, 3, 3, 5),
         (2, 4, 5, 3), (2, 4, 3, 5), (4, 2, 5, 3), (4, 2, 3, 5), (2, 2, Fr(11, 2), Fr(7, 2)), (3, 3, Fr(21, 4), 3)]
for (a, b, p, q) in cases:
    t0 = time.time()
    M = T(a, p); N = T(b, q)
    th = Theta(a, b, p, q)
    vals = []
    for bits in itertools.product([1, -1], repeat=(a + 1) * (b + 1) - 1):
        flat = list(bits) + [-1]
        Y = [flat[i * (b + 1):(i + 1) * (b + 1)] for i in range(a + 1)]
        vals.append((G(Y, M, N), tuple(map(tuple, Y))))
    distinct = sorted(set(v for v, _ in vals), reverse=True)
    assert distinct[0] == th, (a, b, p, q, distinct[0], th)
    top = sorted(Y for v, Y in vals if v == th)
    assert top == sorted([tuple(map(tuple, anti(a, b))), tuple(map(tuple, trunc(a, b)))]), (a, b, p, q)
    for k in (0, 4, 11):
        if k >= len(distinct): continue
        thr = distinct[k]
        bf = sorted(Y for v, Y in vals if v >= thr)
        th2, res, nodes = bnb(a, b, p, q, threshold=thr)
        bb = sorted(tuple(map(tuple, Y)) for g, Y in res)
        assert bf == bb, ("B&B misses/extra", a, b, p, q, k, len(bf), len(bb))
        log(f"({a},{b}) p={p} q={q}: threshold = {k+1}-th largest G value: brute force {len(bf)} matrices == B&B {len(bb)} "
            f"(B&B nodes {nodes}, total {2 ** ((a+1)*(b+1)-1)})")
    log(f"({a},{b}) p={p} q={q}: max G = Theta, maximisers exactly Y-, Y+  [{time.time()-t0:.1f}s]")
