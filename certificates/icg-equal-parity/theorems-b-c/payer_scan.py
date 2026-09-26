"""For each non-A column j<b: min over configurations of s_j/need, grouped by (type, j==0?), for last column in {-A,+B}.
Also: in which configurations does no non-A column j<b pay (s_j >= need) [excluding rank-one]?"""
import itertools, sys
from fractions import Fraction as Fr
from core import T, mus
from colsurplus import decomp
def fmt(Y): return '/'.join(''.join('+' if v > 0 else '-' for v in r) for r in Y)
def run(b, p, q, show=6):
    M = T(2, p); muq = mus(b, q)
    mins = {}; nopay = []
    for bits in itertools.product([1, -1], repeat=3 * (b + 1) - 1):
        Y = [list(bits[0:b + 1]), list(bits[b + 1:2 * b + 2]), list(bits[2 * b + 2:]) + [-1]]
        d = decomp(Y, p, q, M, muq)
        tb, eb = d['types'][b]
        last = ('-' if eb < 0 else '+') + tb
        if last not in ('-A', '+B'): continue
        need = d['need'] if last == '-A' else 4 * (p - 1) * d['rho']
        nonA = [j for j in range(b) if d['types'][j][0] != 'A']
        for j in nonA:
            key = (last, d['types'][j][0], 'j=0' if j == 0 else 'j>0')
            r = d['s'][j] / need
            if key not in mins or r < mins[key][0]: mins[key] = (r, fmt(Y))
        if nonA and all(d['s'][j] < need for j in nonA) and d['kappa'] < need:
            nopay.append((float((sum(d['s']) + d['kappa']) / need), fmt(Y), ''.join(('+' if t[1] > 0 else '-') + t[0] for t in d['types']), Y[0][0]))
    print(f"=== (2,{b}) p={p} q={q}")
    for k in sorted(mins): print(f"   {k}: min s_j/need = {float(mins[k][0]):.4f}  at {mins[k][1]}")
    nopay.sort()
    print(f"   #configs (with a non-A column j<b) where no non-A column pays and kappa<need: {len(nopay)}")
    for x in nopay[:show]: print("      ", x)
    sys.stdout.flush()
if __name__ == "__main__":
    for (b, p, q) in [(2, 5, 3), (2, 3, 5), (2, 7, 3), (2, 11, 3), (2, 3, 7), (4, 5, 3), (4, 3, 5), (4, 7, 3), (4, 5, 7), (4, 3, 7)]:
        run(b, p, q)
