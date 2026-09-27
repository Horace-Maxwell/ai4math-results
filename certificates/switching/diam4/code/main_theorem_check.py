# Consistency check of the Main Theorem constructions (PROOF.md section 9) on all trees of diameter <= 4, n <= N:
#  * family A = T(1^k1, 0^k0), k0 >= 2, k1 >= 2: s_c=+1, one bare leaf -1, middles +1, one far leaf -1;
#  * family B(m) = T(2^m, 0^(m+1)), m >= 2: s_c=+1, bare +1, middles +1, first branch leaves (-,-), others (+,-);
#  * otherwise, if the secular polynomial has <= 1 non-even pair: base switching s+ (construction_I), else s- (centre
#    flipped); if the unique pair is x-1,x+1 and both fail: adjust the largest group (Theorem F2) and retry.
import sys, sympy
from collections import Counter
sys.path.insert(0, '.')
from ht2 import all_ht2, make_s, is_good, build
from constructions import construction_I
from coverage2 import noneven_factors
def s_familyA(a):
    g = Counter(a); k0, k1 = g[0], g[1]
    aa = (0,) * k0 + (1,) * k1
    sigma = [-1] + [1] * (k0 - 1) + [1] * k1       # sigma of bare branches = sign of the bare leaf itself
    mu = [0] * k0 + [1] + [0] * (k1 - 1)           # one far leaf -1
    return aa, 1, sigma, mu
def s_familyB(a):
    m = Counter(a)[2]
    aa = (0,) * (m + 1) + (2,) * m
    sigma = [1] * (2 * m + 1)
    mu = [0] * (m + 1) + [2] + [1] * (m - 1)       # first 2-branch: both leaves -1; others one -1
    return aa, 1, sigma, mu
def adjust_largest(aa, sigma, mu):
    b = max(aa); i = aa.index(b)                   # first branch of the largest group (nondecreasing order)
    mu = list(mu)
    # Target-I pattern: odd b: lambda=-1 or +1/-3; even b: 0/-2.  Increase the leaf sum by 2 (one -1 leaf -> +1),
    # choosing a branch whose new pattern is still non-constant.
    for j in range(i, len(aa)):
        if aa[j] == b and mu[j] >= 1 and (b - 2 * (mu[j] - 1)) < b:
            mu[j] -= 1; return aa, sigma, mu
    return None
N = int(sys.argv[1]); fails = []; stats = Counter()
for n in range(3, N + 1):
    for a in all_ht2(n):
        g = Counter(a)
        famA = set(g) <= {0, 1} and g.get(0, 0) >= 2 and g.get(1, 0) >= 2
        star = set(g) == {0} and g[0] >= 2
        fam10 = set(g) == {0, 1} and g[0] >= 2 and g[1] == 1
        if star:
            k0 = g[0]; aa = (0,) * k0; nflip = 2 if k0 == 4 else 1
            s, adj = make_s(aa, 1, [-1] * nflip + [1] * (k0 - nflip), [0] * k0)
            ok = is_good(aa, s, adj); stats['star' if ok else 'star-FAIL'] += 1
            if not ok: fails.append(('star', a))
            continue
        if fam10:
            k0 = g[0]; aa = (0,) * k0 + (1,)
            s, adj = make_s(aa, 1, [-1] + [1] * (k0 - 1) + [1], [0] * k0 + [1])   # far leaf -1 (L = -1)
            ok = is_good(aa, s, adj); stats['T(1,0^k)' if ok else 'T(1,0^k)-FAIL'] += 1
            if not ok: fails.append(('T10', a))
            continue
        famB = set(g) == {0, 2} and g[0] == g[2] + 1 and g[2] >= 2
        if famA:
            aa, sc, sg, mu = s_familyA(a); s, adj = make_s(aa, sc, sg, mu)
            ok = is_good(aa, s, adj); stats['A' if ok else 'A-FAIL'] += 1
            if not ok: fails.append(('A', a))
            continue
        if famB:
            aa, sc, sg, mu = s_familyB(a); s, adj = make_s(aa, sc, sg, mu)
            ok = is_good(aa, s, adj); stats['B' if ok else 'B-FAIL'] += 1
            if not ok: fails.append(('B', a))
            continue
        ne = noneven_factors(a)
        if len(ne) > 2: stats['>=2 pairs (not claimed)'] += 1; continue
        aa, sg, mu = construction_I(a)
        s1, adj = make_s(aa, 1, sg, mu); s2, _ = make_s(aa, -1, sg, mu)
        if is_good(aa, s1, adj): stats['E/F: s+'] += 1; continue
        if is_good(aa, s2, adj): stats['E/F: s-'] += 1; continue
        adj_ = adjust_largest(aa, sg, mu)
        if adj_ is not None:
            aa3, sg3, mu3 = adj_; s3, _ = make_s(aa3, 1, sg3, mu3); s4, _ = make_s(aa3, -1, sg3, mu3)
            if is_good(aa3, s3, adj) or is_good(aa3, s4, adj): stats['F2: adjusted'] += 1; continue
        stats['FAIL'] += 1; fails.append(('EF', a, [str(f.as_expr()) for f in ne]))
    print(f"n<={n}: {dict(stats)} failures={fails[-3:]}", flush=True)
