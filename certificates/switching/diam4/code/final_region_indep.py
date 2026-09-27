#!/usr/bin/env python3
"""Implementation 2 (independent) of the finite search of PROOF.md section 9.22.
Differences from final_region.py (implementation 1):
  * enumeration uses only the CRUDE per-b* bounds of the proof of Theorem 9.22.2 (no per-B pruning):
      2 N_I + N_II <= Tg := floor(S + 2 + b*/2), S = isqrt(b* - 1);  k0 <= (3S + b* + 4)//2 - 1;
    |L_b| is taken from row_lemmas.L_values (list length), not from a closed formula;
  * integer secular roots are found by a floating-point screen of F(t) = sum k_b/(t - b) over all integers
    1 <= t <= b* + K, t not in B (numpy, vectorised over all multiplicity vectors), and every screened value is
    confirmed exactly with fractions.Fraction (a float screen cannot miss a true root: F(t) = 1 exactly gives
    |F - 1| < 1e-9 in double precision here);
  * for the trees failing the cheap test, the number of non-even pairs is bounded by region_indep.N_upper
    (factor R(t) over Q, certify even orbits by a Rabin irreducibility test of h(x^2) mod p; uncertified orbits
    are counted as non-even), not by factoring R(x^2).
Usage: final_region_indep.py"""
import os, sys, math, itertools
from fractions import Fraction
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from row_lemmas import L_values
from region_indep import N_upper

def Lsize(b, k): return len(L_values(b, k))

total = 0; cheap_surv = []
for bs in range(2, 13):
    S = math.isqrt(bs - 1)
    Tg = (2 * S + 4 + bs) // 2
    k0max = (3 * S + bs + 4) // 2 - 1
    allowed = {b: [k for k in range(1, 3 * Tg + 6) if Lsize(b, k) <= Tg] for b in range(1, bs + 1)}
    allowed[0] = list(range(1, k0max + 1))
    cnt_bs = 0
    for mask in range(1 << bs):
        B = [b for b in range(bs) if mask >> b & 1] + [bs]
        if any(len(allowed[b]) == 0 for b in B): continue
        K = np.array(list(itertools.product(*[allowed[b] for b in B])), dtype=np.int64)   # rows = trees
        if K.size == 0: continue
        M = K.shape[0]; cnt_bs += M
        Bv = np.array(B, dtype=np.float64)
        tmax = bs + int(K.sum(axis=1).max())
        NI = np.zeros(M, dtype=np.int64); Nei = np.zeros(M, dtype=np.int64); Nrat = np.zeros(M, dtype=np.int64)
        Kf = K.astype(np.float64)
        for tv in range(1, tmax + 1):
            if tv in B: continue
            F = Kf @ (1.0 / (tv - Bv))
            hit = np.nonzero(np.abs(F - 1.0) < 1e-9)[0]
            for i in hit:
                if sum(Fraction(int(K[i, j]), tv - B[j]) for j in range(len(B))) == 1:
                    Nrat[i] += 1
                    if math.isqrt(tv) ** 2 == tv: NI[i] += 1
                    elif tv % 2 == 0: Nei[i] += 1
        r = len(B)
        NIIup = (r - Nrat) // 2
        need = 2 * NI + NIIup + 1
        oka = np.zeros(M, dtype=bool)
        for j, b in enumerate(B):
            if b == 0: continue
            Ls = np.array([Lsize(b, int(k)) for k in K[:, j]])
            oka |= Ls >= need
        if 0 in B:
            k0 = K[:, B.index(0)]
            okb = 2 * (k0 + 1) > 4 * NI + 2 * NIIup + Nei
        else:
            okb = np.zeros(M, dtype=bool)
        for i in np.nonzero(~(oka | okb))[0]:
            a = tuple(sorted([b for j, b in enumerate(B) for _ in range(int(K[i, j]))], reverse=True))
            cheap_surv.append((a, int(NI[i]), int(Nei[i])))
    print('b* = %d: trees enumerated %d' % (bs, cnt_bs), flush=True)
    total += cnt_bs
print('INDEP crude region: trees enumerated', total)
print('INDEP survivors of the cheap test:', len(cheap_surv))
final = []
for a, NI, Nei in cheap_surv:
    Nup, unc = N_upper(a)
    NIIup = Nup - NI
    from collections import Counter
    g = Counter(a); k0 = g.get(0, 0)
    oka = any(Lsize(b, g[b]) >= 2 * NI + NIIup + 1 for b in g if b >= 1)
    okb = k0 >= 1 and 2 * (k0 + 1) > 4 * NI + 2 * NIIup + Nei
    print('INDEP SURVIVOR', a, 'N_I=%d N_II<=%d N_ei=%d uncertified=%s' % (NI, NIIup, Nei, unc),
          'covered' if (oka or okb) else 'FAILS')
    if not (oka or okb): final.append(a)
print('INDEP FINAL', len(final), final)
