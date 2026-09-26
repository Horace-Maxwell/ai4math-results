"""(c) Theorem 5 by exhaustive enumeration of sign matrices Y.
Claim: ||T_a(p) Y T_b(q)^T||_1 <= d_a(p) d_b(q), equality iff Y = +-s_a s_b^T  (p>=5, q>=3 real).
Integer (p,q): numpy int64 (exact).  Rational (p,q): exact Fractions for small sizes.
Also informational runs outside the hypotheses."""
import sys, itertools, time
import numpy as np
from fractions import Fraction as Fr
from rv_core import T_gen, T_ram, d_formula, svec, matmul, transpose, l1mat

MAXCELLS = int(sys.argv[1]) if len(sys.argv) > 1 else 20


def exhaustive_int(p, q, a, b, chunk=1 << 17):
    M = np.array(T_gen(a, p), dtype=object).astype(np.int64)
    N = np.array(T_gen(b, q), dtype=object).astype(np.int64)
    ncell = (a + 1) * (b + 1)
    bound = int(d_formula(a, p) * d_formula(b, q))
    best, argbest, total = -1, [], 0
    second = -1
    shifts = np.arange(ncell, dtype=np.int64)
    for start in range(0, 1 << ncell, chunk):
        idx = np.arange(start, min(start + chunk, 1 << ncell), dtype=np.int64)
        bits = (idx[:, None] >> shifts[None, :]) & 1
        Y = (1 - 2 * bits).reshape(-1, a + 1, b + 1)
        V = np.abs(np.matmul(np.matmul(M, Y), N.T)).sum(axis=(1, 2))
        total += len(idx)
        mx = int(V.max())
        if mx > best:
            if best >= 0:
                second = max(second, best)
            best, argbest = mx, [Y[k].copy() for k in np.nonzero(V == mx)[0]]
        elif mx == best:
            argbest += [Y[k].copy() for k in np.nonzero(V == mx)[0]]
        # track second largest distinct value
        vals = V[V < best]
        if vals.size:
            second = max(second, int(vals.max()))
    S = np.outer(svec(a), svec(b)).astype(np.int64)
    arg_ok = len(argbest) == 2 and all(np.array_equal(Yb, S) or np.array_equal(Yb, -S) for Yb in argbest)
    return best, bound, len(argbest), arg_ok, second, total


def exhaustive_frac(p, q, a, b):
    M, N = T_gen(a, p), T_gen(b, q)
    Nt = transpose(N)
    bound = d_formula(a, p) * d_formula(b, q)
    best, arg = None, []
    for signs in itertools.product([1, -1], repeat=(a + 1) * (b + 1)):
        Y = [list(signs[i * (b + 1):(i + 1) * (b + 1)]) for i in range(a + 1)]
        v = l1mat(matmul(matmul(M, Y), Nt))
        if best is None or v > best:
            best, arg = v, [Y]
        elif v == best:
            arg.append(Y)
    S = [[(-1) ** (i + j) for j in range(b + 1)] for i in range(a + 1)]
    negS = [[-e for e in r] for r in S]
    ok = len(arg) == 2 and all(Y in (S, negS) for Y in arg)
    return best, bound, len(arg), ok


t0 = time.time()
shapes = [(a, b) for a in range(1, 20) for b in range(1, 20) if (a + 1) * (b + 1) <= MAXCELLS]
shapes.sort(key=lambda s: (s[0] + 1) * (s[1] + 1))
allok = True
print('=== integer (p,q), exhaustive, (a+1)(b+1) <= %d ===' % MAXCELLS)
for (p, q) in [(5, 3), (7, 3), (5, 4)]:
    # confirm the T used for prime p,q equals the Ramanujan-sum construction
    for a in range(1, 6):
        if p in (5, 7):
            assert T_ram(a, p) == [[int(v) for v in r] for r in T_gen(a, p)]
        if q == 3:
            assert T_ram(a, q) == [[int(v) for v in r] for r in T_gen(a, q)]
    for (a, b) in shapes:
        best, bound, nmax, arg_ok, second, total = exhaustive_int(p, q, a, b)
        ok = (best == bound) and arg_ok
        allok &= ok
        print('(p,q)=(%d,%d) (a,b)=(%d,%d) #Y=%d  max=%d  d_a d_b=%d  #argmax=%d  argmax=+-s s^T:%s  2nd=%d (ratio %.5f)  %s'
              % (p, q, a, b, total, best, bound, nmax, arg_ok, second, second / bound, 'OK' if ok else 'FAIL'))
        sys.stdout.flush()
print('integer part all OK:', allok, ' time %.1fs' % (time.time() - t0))

print('=== rational (p,q), exact Fractions, (a+1)(b+1) <= 9 ===')
allok2 = True
for (p, q) in [(Fr(5), Fr(3)), (Fr(11, 2), Fr(3)), (Fr(5), Fr(13, 4)), (Fr(17, 3), Fr(7, 2)), (Fr(21, 4), Fr(31, 10))]:
    for (a, b) in [(1, 1), (1, 2), (2, 1), (1, 3), (3, 1), (2, 2)]:
        best, bound, nmax, ok = exhaustive_frac(p, q, a, b)
        good = best == bound and ok
        allok2 &= good
        print('(p,q)=(%s,%s) (a,b)=(%d,%d) max=%s bound=%s #argmax=%d argmax ok=%s %s'
              % (p, q, a, b, best, bound, nmax, ok, 'OK' if good else 'FAIL'))
print('rational part all OK:', allok2)

print('=== informational, outside hypotheses (integer, exhaustive, (a+1)(b+1)<=12) ===')
for (p, q) in [(3, 3), (4, 3), (5, 2), (3, 5)]:
    for (a, b) in [s for s in shapes if (s[0] + 1) * (s[1] + 1) <= 12]:
        best, bound, nmax, arg_ok, second, total = exhaustive_int(p, q, a, b)
        print('(p,q)=(%d,%d) (a,b)=(%d,%d) max=%d d_a d_b=%d #argmax=%d argmax ok=%s'
              % (p, q, a, b, best, bound, nmax, arg_ok))
print('total time %.1fs' % (time.time() - t0))
