# Consistency check of the Row Lemmas: for every tree T(a) with n <= Nmax satisfying criterion (a) (resp. (b)),
# at least one candidate of the corresponding family is a good switching (exact Bareiss rank over Q), and all
# candidates satisfy (L) and (Z) [checked implicitly: a good candidate must exist; we also count good candidates].
import sys
sys.path.insert(0, '.')
from ht2 import all_ht2, make_s, is_good
from row_lemmas import criteria, L_values, leaf_row_switch, bare_row_switch
from collections import Counter
N0, N1 = int(sys.argv[1]), int(sys.argv[2])
bad = []; cnt = Counter()
for n in range(N0, N1 + 1):
    for a in all_ht2(n):
        g = Counter(a)
        if not any(b >= 2 for b in g): continue
        c = criteria(a)
        if c['a']:
            beta, _ = c['a']; ok = False; ngood = 0; tot = 0
            for Lam in L_values(beta, g[beta]):
                for eps in (1, -1):
                    aa, sc, sg, mu = leaf_row_switch(a, beta, Lam, eps)
                    s, adj = make_s(aa, sc, sg, mu); tot += 1
                    if is_good(aa, s, adj): ngood += 1
            cnt['a'] += 1
            if ngood == 0: bad.append(('a', a))
            if tot - ngood > 4 * c['N']: bad.append(('a-count', a, tot, ngood, c['N']))
        if c['b']:
            k0 = g[0]; ngood = 0; tot = 0
            for m in range(0, k0 + 1):
                for eps in (1, -1):
                    aa, sc, sg, mu = bare_row_switch(a, m, eps)
                    s, adj = make_s(aa, sc, sg, mu); tot += 1
                    if is_good(aa, s, adj): ngood += 1
            cnt['b'] += 1
            if ngood == 0: bad.append(('b', a))
            if tot - ngood > 4 * c['N'] + c['Nei']: bad.append(('b-count', a, tot, ngood, c['N'], c['Nei']))
    print(f"n<={n}: checked {dict(cnt)}; violations {bad[-3:]} (total {len(bad)})", flush=True)
