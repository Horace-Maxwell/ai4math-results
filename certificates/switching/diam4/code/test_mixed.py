import sys
sys.path.insert(0, '.')
from ht2 import all_ht2, make_s, is_good
from constructions import construction_mixed
from diagnose import bad_factors
N = int(sys.argv[1])
opts = [dict(S_all=False, b1_mode='sigma'), dict(S_all=True, b1_mode='sigma'), dict(S_all=False, b1_mode='lambda'), dict(S_all=True, b1_mode='lambda')]
fails = {i: [] for i in range(len(opts))}; none = []; tot = 0
for n in range(3, N + 1):
    for a in all_ht2(n):
        tot += 1; ok = False
        for i, o in enumerate(opts):
            aa, sg, mu = construction_mixed(a, **o); s, adj = make_s(aa, 1, sg, mu)
            if is_good(aa, s, adj): ok = True
            else: fails[i].append(a)
        if not ok: none.append(a)
print('trees', tot)
for i in fails: print(opts[i], 'fails', len(fails[i]), fails[i][:15])
print('none works', len(none), none[:20])
