"""Item 8: exhaustive exact maximisation of G(Y) over ALL sign matrices Y in {+-1}^{3 x (b+1)} with Y_{2b} = -1,
shapes (2,2), (2,4), (2,6), (2,8), for prime pairs and non-integer real pairs in the stated range.

Exact integer arithmetic: for p = u/v, q = x/y the matrices v^2 T_2(p) and y^b T_b(q) are integral; G scales by v^2 y^b.
Vectorisation: W_k = N y_k for all sign vectors y_k (table), Z_i = sum_k M_ik W_k; loop over the last row y_2 (corner -1),
broadcast over (y_0, y_1).  An explicit a-priori bound excludes int64 overflow.
Reports: max G, whether max G == Theta, the list of maximisers (must be exactly {Y-, Y+}), and the second-largest value.
"""
import sys, time, itertools
from fractions import Fraction as Fr
import numpy as np
from rv_common import T, Theta, Yminus, Yplus

out = []
def log(s):
    print(s); sys.stdout.flush(); out.append(s)


def int_scaled(k, x):
    x = Fr(x)
    Tm = T(k, x)
    den = 1
    for row in Tm:
        for v in row:
            den = den * v.denominator // np.gcd(den, v.denominator)
    # use the canonical scale x.denominator^(power) to keep it simple and exact
    S = den
    Mi = np.array([[int(v * S) for v in row] for row in Tm], dtype=np.int64)
    assert all(Fr(int(v * S)) == v * S for row in Tm for v in row)
    return Mi, S


def run(b, p, q, report_second=True):
    t0 = time.time()
    M, SM = int_scaled(2, p)
    N, SN = int_scaled(b, q)
    scale = SM * SN
    Th = Theta(2, b, p, q) * scale
    assert Th.denominator == 1
    Th = int(Th)
    nb = b + 1
    # a-priori bound: |Z_ij| <= (max_i sum_k |M_ik|) (max_j sum_l |N_jl|); |G| <= 3(b+1) * that
    bound = int(np.abs(M).sum(axis=1).max()) * int(np.abs(N).sum(axis=1).max()) * 3 * nb
    assert bound < 2 ** 62, "overflow risk"
    signs = np.array(list(itertools.product((1, -1), repeat=nb)), dtype=np.int64)   # all sign vectors (rows)
    W = signs @ N.T                    # W[y] = N y
    last_rows = np.where(signs[:, -1] == -1)[0]
    best = None; arg = []; second = None
    W0 = W[:, None, :]; W1 = W[None, :, :]
    for r2 in last_rows:
        W2 = W[r2][None, None, :]
        Z0 = M[0, 0] * W0 + M[0, 1] * W1 + M[0, 2] * W2
        Z1 = M[1, 0] * W0 + M[1, 1] * W1 + M[1, 2] * W2
        Z2 = M[2, 0] * W0 + M[2, 1] * W1 + M[2, 2] * W2
        Gv = np.abs(Z0).sum(-1) + np.abs(Z1).sum(-1) + np.abs(Z2[..., :-1]).sum(-1) + Z2[..., -1]
        mx = int(Gv.max())
        # track best and second best distinct values
        vals = np.unique(Gv)[-2:]
        for v in vals:
            v = int(v)
            if best is None or v > best:
                if best is not None and (second is None or best > second):
                    second = best
                best = v; arg = []
            elif v < best and (second is None or v > second):
                second = v
        if mx == best:
            for (i0, i1) in zip(*np.nonzero(Gv == best)):
                arg.append((tuple(signs[i0]), tuple(signs[i1]), tuple(signs[r2])))
    Ym = Yminus(2, b); Yp = Yplus(2, b)
    expected = {tuple(tuple(r) for r in Ym), tuple(tuple(r) for r in Yp)}
    got = set(arg)
    ok = (best == Th) and (got == expected) and len(arg) == 2
    gap = Fr(best - second, scale) if second is not None else None
    log(f"(2,{b}) p={p} q={q}: max G = {Fr(best, scale)}, Theta = {Fr(Th, scale)}, equal={best == Th}, "
        f"maximisers exactly {{Y-,Y+}}: {got == expected and len(arg) == 2}; next value below max: gap {gap} "
        f"({time.time() - t0:.1f}s)")
    return ok


allok = True
primes_pairs = [(3, 5), (5, 3), (3, 7), (7, 3), (5, 7), (7, 5), (3, 11), (11, 3), (3, 101), (101, 3), (11, 13), (13, 11),
                (3, 1009), (1009, 3)]
real_pairs = [(Fr(5), Fr(3)), (Fr(3), Fr(5)),                       # boundary corners (P,Q) = (4,2), (2,4)
              (Fr(11, 2), Fr(7, 2)), (Fr(5), Fr(10, 3)), (Fr(51, 10), Fr(31, 10)), (Fr(41, 4), Fr(3)),
              (Fr(3), Fr(11, 2)), (Fr(3), Fr(51, 10)), (Fr(3), Fr(41, 4)), (Fr(21, 4), Fr(21, 4))]
for b in (2, 4):
    for (p, q) in primes_pairs + real_pairs:
        allok &= run(b, p, q)
for (p, q) in [(3, 5), (5, 3), (3, 7), (7, 3), (5, 7), (7, 5), (3, 101), (101, 3), (11, 13), (13, 11), (1009, 3),
               (Fr(11, 2), Fr(7, 2)), (Fr(3), Fr(11, 2)), (Fr(51, 10), Fr(31, 10)), (Fr(3), Fr(41, 4))]:
    allok &= run(6, p, q)
for (p, q) in [(3, 5), (5, 3), (7, 3), (3, 7), (Fr(11, 2), Fr(7, 2)), (Fr(3), Fr(11, 2))]:
    allok &= run(8, p, q)
log(f"ALL {'OK' if allok else 'NOT OK'}")
