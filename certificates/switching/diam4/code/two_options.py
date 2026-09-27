# Option 1: rule R_A (s_c = +1).  Option 2: same leaf/middle signs, centre flipped (s_c = -1).
import sys
sys.path.insert(0, '.')
from ht2 import all_ht2, make_s, is_good
from rules import rule_switch, VARIANTS
from diagnose import bad_factors
N = int(sys.argv[1]); tot = 0; f1 = []; f2 = []; both = []
for n in range(3, N + 1):
    for a in all_ht2(n):
        tot += 1
        aa, sigma, mu = rule_switch(a, VARIANTS[0])
        s1, adj = make_s(aa, 1, sigma, mu)
        s2, _ = make_s(aa, -1, sigma, mu)
        g1 = is_good(aa, s1, adj); g2 = is_good(aa, s2, adj)
        if not g1: f1.append(a)
        if not g2: f2.append(a)
        if not g1 and not g2:
            both.append(a); print('BOTH FAIL', n, a, bad_factors(aa, s1), bad_factors(aa, s2), flush=True)
    print(f'n<={n} trees={tot} opt1 fails={len(f1)} opt2 fails={len(f2)} both={len(both)}', flush=True)
