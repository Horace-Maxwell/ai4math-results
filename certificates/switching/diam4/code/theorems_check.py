# Membership in the proven classes D1, D1+, D2, D3 (PROOF.md section 9) and exact check of the corresponding
# explicit switchings, for all trees of diameter <= 4 with n <= N.  Also reports coverage.
import sys
from fractions import Fraction
from collections import Counter
sys.path.insert(0, '.')
from ht2 import all_ht2, make_s, is_good
from constructions import construction_I, construction_II

def secular_at(a, tval):
    """F(t) = sum_b k_b/(t-b) evaluated exactly at rational t (None if t is a pole)"""
    g = Counter(a); s = Fraction(0)
    for b, kb in g.items():
        if tval == b: return None
        s += Fraction(kb, 1) / (tval - b)
    return s

def is_cube(m):
    c = round(m ** (1 / 3))
    for x in (c - 1, c, c + 1):
        if x >= 0 and x ** 3 == m: return x
    return None

def classes(a):
    g = Counter(a); k0 = g.get(0, 0); k1 = g.get(1, 0)
    E_odd = [b for b in g if b >= 2 and b % 2 == 0 and g[b] % 2 == 1]
    O_odd = [b for b in g if b % 2 == 1 and g[b] % 2 == 1]
    out = []
    if k0 == 0 and not E_odd: out.append('D1')
    if k0 == 0 and len(E_odd) == 1 and k1 <= 1: out.append('D1+')
    if k0 >= 1 and not E_odd and k1 <= 1 and any(b >= 2 for b in g):
        m = is_cube(k0)
        if m is None or secular_at(a, Fraction(m * m)) != 1: out.append('D3')
    if not O_odd:
        excluded = (set(g) <= {0, 1, 2} and g.get(2, 0) == 2 and k0 >= 1) or tuple(sorted(a)) == (0, 0, 0, 0)
        t1 = (k1 == 0 and secular_at(a, Fraction(1)) == 1)
        if not excluded and not t1: out.append('D2')
    return out

if __name__ == '__main__':
    N = int(sys.argv[1])
    for n in range(3, N + 1):
        tot = cov = 0; fails = []; cnt = Counter()
        for a in all_ht2(n):
            tot += 1; cl = classes(a)
            if cl: cov += 1
            for c in cl:
                cnt[c] += 1
                aa, sg, mu = construction_II(a) if c == 'D2' else construction_I(a)
                s, adj = make_s(aa, 1, sg, mu)
                if not is_good(aa, s, adj): fails.append((c, a))
        print(f"n={n} trees={tot} covered_by_D1..D3={cov} ({100*cov/tot:.1f}%) per_class={dict(cnt)} construction_failures={fails[:5]}", flush=True)
