# For each T(a) (n <= N): does a good switching exist with s_c = +1, sigma_i = +1 for all branches with a_i >= 1,
# bare branches (a_i = 0): sigma = +1 except the first j of them (j = 0 or 1), and arbitrary leaf patterns
# (mu_i = number of -1 leaves, up to symmetry within groups)?  Exact certificate (Bareiss rank over Q).
import sys, itertools
sys.path.insert(0, '.')
from ht2 import all_ht2, make_s, is_good, build
from collections import Counter
N = int(sys.argv[1])
fails = []; tot = 0
for n in range(3, N + 1):
    for a in all_ht2(n):
        tot += 1
        k = len(a); groups = Counter(a)
        found = None
        # group-wise multisets of mu values
        per_group = []
        for b in sorted(groups):
            kb = groups[b]
            per_group.append((b, list(itertools.combinations_with_replacement(range(b + 1), kb))))
        k0 = groups.get(0, 0)
        for j0 in ([0, 1] if k0 >= 2 else [0]):
            for choice in itertools.product(*[pg[1] for pg in per_group]):
                mu = []; sigma = []
                zero_seen = 0
                for (b, _), mus in zip(per_group, choice):
                    for m in mus:
                        mu.append(m)
                        if b == 0:
                            sigma.append(-1 if zero_seen < j0 else 1); zero_seen += 1
                        else: sigma.append(1)
                # reorder to match a's order (a is nonincreasing; per_group sorted increasing)
                order = []
                for (b, _), mus in zip(per_group, choice):
                    order += [b] * len(mus)
                # build a' in increasing order and use it
                aa = tuple(order)
                s, adj = make_s(aa, 1, sigma, mu)
                if is_good(aa, s, adj):
                    found = (j0, choice); break
            if found: break
        if not found: fails.append(a)
    print(f"n<={n}: trees so far {tot}, no sigma=1-type solution: {len(fails)}  {fails[-5:]}", flush=True)
