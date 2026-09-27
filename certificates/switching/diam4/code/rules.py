# Candidate explicit rules for a good switching of T(a); s_c = +1 always (global sign is irrelevant).
import sys
sys.path.insert(0, '.')
from ht2 import all_ht2, make_s, is_good
from collections import Counter

def group_lambdas(b, kb, variant):
    """leaf sums for the kb branches with b leaves; variant selects the tie-breaking choices"""
    if b == 0: return [0] * kb
    if b % 2 == 1:
        lam = [-1] * kb
        if kb >= 2:
            if b >= 3: lam[0], lam[1] = 1, -3
            else: lam[0] = 1          # b == 1: variation forces a +1
        if variant.get('odd_single_plus') and kb == 1: lam[0] = 1
        return lam
    else:
        lam = [0 if j % 2 == 0 else -2 for j in range(kb)]
        if kb % 2 == 1 and variant.get('even_odd_minus'):
            lam[-1] = -2 if kb == 1 else lam[-1]
            if kb >= 3: lam[0] = -2; lam[1] = 0; lam[2] = -2 if kb >= 3 else lam[2]
        return lam

def rule_switch(a, variant):
    groups = Counter(a); bs = sorted(groups)
    aa = []; sigma = []; mu = []
    k0 = groups.get(0, 0)
    has_big = any(b >= 2 for b in bs)
    j0 = variant.get('j0', None)
    if j0 is None:
        j0 = 0
        if k0 >= 2 and not has_big: j0 = 1
    for b in bs:
        kb = groups[b]
        lam = group_lambdas(b, kb, variant)
        for j in range(kb):
            aa.append(b)
            if b == 0:
                sigma.append(-1 if j < j0 else 1); mu.append(0)
            else:
                sigma.append(1); mu.append((b - lam[j]) // 2)
    return tuple(aa), sigma, mu

VARIANTS = [
    dict(),
    dict(even_odd_minus=True),
    dict(odd_single_plus=True),
    dict(odd_single_plus=True, even_odd_minus=True),
]

if __name__ == '__main__':
    N = int(sys.argv[1])
    fails = {i: [] for i in range(len(VARIANTS))}; none = []; tot = 0
    for n in range(3, N + 1):
        for a in all_ht2(n):
            tot += 1; ok_any = False
            for vi, var in enumerate(VARIANTS):
                aa, sigma, mu = rule_switch(a, var)
                s, adj = make_s(aa, 1, sigma, mu)
                if is_good(aa, s, adj): ok_any = True
                else: fails[vi].append(a)
            if not ok_any: none.append(a)
    print('trees', tot)
    for vi in fails: print('variant', vi, VARIANTS[vi], 'fails', len(fails[vi]), fails[vi][:12])
    print('no variant works:', len(none), none[:20])
