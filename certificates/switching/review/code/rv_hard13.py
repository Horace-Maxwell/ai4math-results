#!/usr/bin/env python3
"""Referee: targeted search for trees with b* >= 13 and >= 2 perfect-square secular roots (worst case of Thm 9.22.2),
then full b*-row test (exact goodness of every member) and bad-count check."""
import random, math, sys, time
from rv_region import int_secular_roots
from rv_rows import test_tree
rng = random.Random(int(sys.argv[1])); T0 = time.time(); found = {}
while time.time() - T0 < float(sys.argv[2]):
    bstar = rng.randint(13, 40)
    vals = sorted(set([bstar] + [rng.randint(0, bstar) for _ in range(rng.randint(1, 5))]))
    a = []
    for v in vals: a += [v] * rng.choice([1, 1, 1, 2, 2, 3, 4, 6, 9])
    a = tuple(sorted(a, reverse=True))
    if 1 + len(a) + sum(a) > 160 or a in found: continue
    rts = int_secular_roots(a)
    sq = [t for t in rts if math.isqrt(t) ** 2 == t]
    if len(sq) >= 2: found[a] = sq
print('found %d trees with b*>=13 and >=2 square secular roots' % len(found), flush=True)
viol = 0
for a, sq in sorted(found.items(), key=lambda x: -len(x[1]))[:60]:
    r = test_tree(a); a, n, NI, NII, Nei, rep = r
    rb = [x for x in rep if x[0] == 'leaf' and x[1] == max(a)][0]
    ok = rb[2] <= rb[4] and rb[3] > 0 and rb[5]
    viol += (not ok)
    print('ok' if ok else 'VIOLATION', a, 'n=%d N_I=%d N_II=%d squares=%s  row b*=%d: bad %d of %d (bound %d)' % (n, NI, NII, sq, max(a), rb[2], rb[2] + rb[3], rb[4]), flush=True)
print('SUMMARY violations', viol)
