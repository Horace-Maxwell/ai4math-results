import sys
sys.path.insert(0, '.')
from ht2 import all_ht2, make_s, is_good
from constructions import construction_I, construction_II, in_class_D1, in_class_D2
N = int(sys.argv[1]); tot = c1 = c2 = both = 0; bad1 = []; bad2 = []; neither = 0
for n in range(3, N + 1):
    for a in all_ht2(n):
        tot += 1
        i1, i2 = in_class_D1(a), in_class_D2(a)
        if i1:
            c1 += 1
            aa, sg, mu = construction_I(a); s, adj = make_s(aa, 1, sg, mu)
            if not is_good(aa, s, adj): bad1.append(a)
        if i2:
            c2 += 1
            aa, sg, mu = construction_II(a); s, adj = make_s(aa, 1, sg, mu)
            if not is_good(aa, s, adj): bad2.append(a)
        if i1 and i2: both += 1
        if not i1 and not i2: neither += 1
    print(f"n<={n}: trees {tot}; class D1 {c1} (fail {len(bad1)}); class D2 {c2} (fail {len(bad2)}); in both {both}; in neither {neither}", flush=True)
print('D1 failures', bad1[:10]); print('D2 failures', bad2[:10])
