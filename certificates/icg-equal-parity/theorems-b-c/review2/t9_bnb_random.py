"""Referee-2: branch and bound (bnb.py) at random rational parameter points of both regions, and at large b.
Checks max G = Theta with exactly the two maximisers Y-, Y+.  Single process."""
import random, time
from fractions import Fraction as Fr
from bnb import bnb
from r2core import anti, trunc

random.seed(4242)
out = open('logs/t9_bnb_random.log', 'w')
def log(*a):
    s = ' '.join(str(x) for x in a); print(s, flush=True); out.write(s + '\n'); out.flush()

def check(a, b, p, q):
    th, res, nodes = bnb(a, b, p, q)
    Ys = sorted(tuple(map(tuple, Y)) for g, Y in res)
    ok = Ys == sorted([tuple(map(tuple, anti(a, b))), tuple(map(tuple, trunc(a, b)))]) and all(g == th for g, Y in res)
    return ok, nodes

t0 = time.time()
n = 0; bad = []
for (a, b) in [(3, 3), (3, 5), (3, 7), (3, 9), (4, 4), (4, 6), (4, 8), (3, 1), (4, 2)]:
    for trial in range(60):
        if trial % 2 == 0:
            p = Fr(5) + Fr(random.randint(0, 400), random.randint(1, 60)); q = Fr(3) + Fr(random.randint(0, 400), random.randint(1, 60))
        else:
            p = Fr(3); q = Fr(5) + Fr(random.randint(0, 400), random.randint(1, 60))
        if trial < 4:   # corners of the regions
            p, q = [(Fr(5), Fr(3)), (Fr(3), Fr(5)), (Fr(5), Fr(3) + Fr(1, 1000)), (Fr(5) + Fr(1, 1000), Fr(3))][trial]
        ok, nodes = check(a, b, p, q)
        n += 1
        if not ok: bad.append((a, b, p, q))
    log(f"({a},{b}): 60 parameter points (corners + random rationals in both regions): {'OK' if not bad else bad[:3]}")
for (a, b) in [(3, 31), (3, 41), (4, 30), (4, 40), (5, 25), (6, 20)]:
    for (p, q) in [(Fr(5), Fr(3)), (Fr(3), Fr(5)), (Fr(7), Fr(3)), (Fr(11, 2), Fr(7, 2))]:
        ok, nodes = check(a, b, p, q)
        n += 1
        if not ok: bad.append((a, b, p, q))
        log(f"({a},{b}) p={p} q={q}: {'OK' if ok else 'FAIL'} (nodes {nodes})")
log(f"total {n} B&B runs, failures {len(bad)}  [{time.time()-t0:.0f}s]")
