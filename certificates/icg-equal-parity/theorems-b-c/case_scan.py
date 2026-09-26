"""Scan all Y for shape (2,b): classify by (last column type, u_0), report min margin (total) and min ratio of
(sum s_j + rho*Delta(c_b) + kappa) / need, and the argmin configurations. Also: does a single column pay?"""
import itertools, sys
from fractions import Fraction as Fr
from core import T, mus
from colsurplus import decomp
def fmt(Y): return '/'.join(''.join('+' if v > 0 else '-' for v in r) for r in Y)
def run(b, p, q, show=4):
    M = T(2, p); muq = mus(b, q)
    stats = {}
    for bits in itertools.product([1, -1], repeat=3 * (b + 1) - 1):
        Y = [list(bits[0:b + 1]), list(bits[b + 1:2 * b + 2]), list(bits[2 * b + 2:]) + [-1]]
        d = decomp(Y, p, q, M, muq)
        tb, eb = d['types'][b]
        key = (('-' if eb < 0 else '+') + tb, Y[0][0])
        avail = sum(d['s']) + d['sb'] + d['kappa']
        ratio = avail / d['need']
        single = max([d['sb'] + d['kappa']] + d['s']) / d['need']
        st = stats.setdefault(key, [])
        st.append((ratio, single, fmt(Y), [str(t[1] > 0 and '+' or '-') + t[0] for t in d['types']]))
    print(f"=== (2,{b}) p={p} q={q}")
    for key in sorted(stats):
        L = sorted(stats[key])
        nsingle_fail = sum(1 for r in L if r[1] < 1)
        print(f"  last={key[0]} u0={key[1]:+d}: n={len(L)} min ratio={float(L[0][0]):.4f}  #no-single-payer={nsingle_fail}")
        for r in L[:show]:
            print(f"      ratio={float(r[0]):.4f} single={float(r[1]):.4f} Y={r[2]} types={''.join(r[3])}")
    sys.stdout.flush()
if __name__ == "__main__":
    for (b, p, q) in [(2, 5, 3), (2, 3, 5), (2, 7, 3), (4, 5, 3), (4, 3, 5), (4, 7, 3), (4, 11, 3), (4, 5, 7), (4, 3, 7)]:
        run(b, p, q)
