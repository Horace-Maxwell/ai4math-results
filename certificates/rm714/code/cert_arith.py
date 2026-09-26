#!/usr/bin/env python3
"""cert_arith.py -- implementation 1 (Python) of the finite arithmetic certificates used in
Propositions C, C', D and Lemma F of PROOF.md.  Implementation 2 is cert_arith.c (written
separately; shares no code).  Both print the same canonical lines; the logs are diffed.

Cited inputs (not re-proved): the weights of RM(6,12) below 160 (Kasami-Tokura / KTA, as quoted
in Lou-Wang, arXiv:2406.03803v1, Lemma 2) and, for 160..166, Lou-Wang's theorem that every even
weight in [160, 4096-160] occurs.  The weights of RM(6,13) below 256 (Kasami-Tokura)."""
U0 = [322, 326, 330, 334]
UD = U0 + [16384 - w for w in U0]   # D is checked on all of U
L6 = [0, 64, 96, 112, 120, 124, 126, 128, 136, 144, 148, 152, 154, 156, 158, 160, 162, 164, 166]
out = []

# C1 / C': triangle-feasible weight triples (a<=b<=c, a+b+c=w, c<=a+b) from L6
for w in U0:
    T = [(a, b, c) for a in L6 for b in L6 for c in L6 if a <= b <= c and a + b + c == w and c <= a + b]
    out.append("C triples w=%d: %s" % (w, " ".join("(%d,%d,%d)" % t for t in T) or "none"))
# every c in a feasible triple is <= w/2 <= 167, so L6 (all weights <= 167) is sufficient
out.append("C max needed weight: %d" % max(w // 2 for w in U0))

# C': overlaps |X cap Y| = (wt X + wt Y - wt(X+Y))/2 used in the proof
for (x, y, z) in [(64, 126, 136), (64, 126, 144), (64, 112, 154), (64, 112, 158), (96, 126, 112)]:
    out.append("C' overlap wt=%d,%d sum=%d: %d" % (x, y, z, (x + y - z) // 2))
P2 = [0] + [2 ** j for j in range(0, 7)]          # possible |6-flat cap 6-flat| in F_2^12
for s in [23, 25, 27, 29]:
    ok = any(p + q == s for p in P2 for q in P2)
    out.append("C' %d is sum of two of {0,1,2,...,64}: %s" % (s, ok))
for (target, ts) in [(11, [0, 1]), (9, [0, 1])]:
    sols = [(t, target - 1 + 2 * t) for t in ts if (target - 1 + 2 * t) in P2]
    out.append("C' 1+2^j-2t=%d solutions (t,2^j): %s" % (target, sols or "none"))
out.append("C' (96,112,126) bound 3+48=%d < 55: %s" % (3 + 48, 3 + 48 < 55))

# D: flats F1,F2 (dim 7, meeting in one point p), F3 of dim d in 7..14
solsA = []
for d in range(7, 15):
    for w in UD:
        rhs = 2 ** d + 258 - w
        for a in range(1, 8):
            for b in range(a, 8):
                if 2 ** (a + 1) + 2 ** (b + 1) == rhs:
                    solsA.append((d, w, a, b, a + b <= d))
out.append("D p in F3 solutions (d,w,a,b,a+b<=d): %s" % (" ".join(str(s) for s in solsA) or "none"))
PB = [0] + [2 ** j for j in range(1, 8)]
solsB = []
for d in range(7, 15):
    for w in UD:
        rhs = 2 ** (d - 1) + 127 - w // 2
        for al in PB:
            for be in PB:
                if al <= be and al + be == rhs:
                    solsB.append((d, w, al, be))
out.append("D p notin F3 solutions (d,w,alpha,beta): %s" % (" ".join(str(s) for s in solsB) or "none"))
two = set()
for a in range(7, 15):
    for b in range(7, 15):
        lo = max(0, a + b - 14)
        for inter in [0] + [2 ** j for j in range(lo, min(a, b) + 1)]:
            wt = 2 ** a + 2 ** b - 2 * inter
            if wt % 4 == 2:
                two.add(wt)
out.append("D two flats, weights = 2 mod 4: %s" % sorted(two))
out.append("D three pairwise transversal 7-flats: %s" % sorted({384 - 6 + 4 * t for t in (0, 1)}))

# F2/F3: sum_a n_a = C(w,2) versus 3*(2^14-1)
for w in U0:
    cw = w * (w - 1) // 2
    out.append("F3 w=%d C(w,2)=%d > %d: %s -> wt h <= %d" % (w, cw, 3 * 16383, cw > 3 * 16383, w - 10))
# F6: directions with n_a in {1,3}: #{a : n_a >= 5} <= (C(w,2) - 16383)/4
for w in U0:
    cw = w * (w - 1) // 2
    bad = (cw - 16383) // 4
    out.append("F6 w=%d C(w,2)=%d < 5*16383=%d: %s; directions with n_a in {1,3} >= %d; wt h in {%d, %d}" % (w, cw, 5 * 16383, cw < 5 * 16383, 16383 - bad, w - 2, w - 6))
# F4: smallest s = 2 mod 4 with s^2 >= (2^14 w - w^2)/(2^14-1); light side <= (w-s)/2
for w in U0:
    num = 16384 * w - w * w
    s = 2
    while s * s * 16383 < num:
        s += 4
    out.append("F4 w=%d num=%d s_min=%d light<=%d" % (w, num, s, (w - s) // 2))
# F5: w=322 = 128 + wt h - 2t, t odd, wt h in KT range of RM(6,13) below 256
KT613 = [128, 192, 224, 240, 248, 252]
F5 = [(wh, (128 + wh - 322) // 2) for wh in KT613 if (128 + wh - 322) > 0 and ((128 + wh - 322) // 2) % 2 == 1]
out.append("F5 (wt h, t): %s" % F5)
for (wh, t) in F5:
    cand = [(s, t - 1 + 2 * s) for s in (0, 1) if (t - 1 + 2 * s) in [2 ** j for j in range(0, 7)]]
    out.append("F5 two-flat form (KT type II) wt h=%d t=%d: (s, |F cap B|) powers of two: %s" % (wh, t, cand or "none"))
print("\n".join(out))
