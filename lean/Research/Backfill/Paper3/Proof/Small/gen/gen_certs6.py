#!/usr/bin/env python3
# Paper 3, version 2: the table `certs6` of `Small/Defs.lean` (data only; every certificate
# is checked by the Lean kernel, nothing here is trusted). Run: python3 gen_certs6.py
# Generate isomorphism certificates for the 70 labelled cubic graphs on {0..5}.
# Representation: pair {i<j} -> bit j*(j-1)/2 + i of the mask; permutation code: sum pi(i) << (3 i).
import itertools
def pidx(i, j):
    if i > j: i, j = j, i
    return j * (j - 1) // 2 + i
def adj(c, i, j):
    return i != j and (c >> pidx(i, j)) & 1 == 1
def mask_of(edges):
    c = 0
    for (i, j) in edges:
        c |= 1 << pidx(i, j)
    return c
K33 = mask_of([(i, 3 + j) for i in range(3) for j in range(3)])
# prism K3 x K2, vertex (a, b) -> 2 a + b
pe = []
for a in range(3):
    for b in range(2):
        for a2 in range(3):
            for b2 in range(2):
                u, v = 2 * a + b, 2 * a2 + b2
                if u < v and ((a != a2 and b == b2) or (a == a2 and b != b2)):
                    pe.append((u, v))
PRISM = mask_of(pe)
print("K33 mask", K33, "prism mask", PRISM, "prism edges", pe)
perms = list(itertools.permutations(range(6)))
def iso(c, t, p):
    return all(adj(c, i, j) == adj(t, p[i], p[j]) for i in range(6) for j in range(6))
certs = []
for c in range(1 << 15):
    if all(sum(adj(c, i, j) for j in range(6)) == 3 for i in range(6)):
        found = None
        for flag, t in ((False, K33), (True, PRISM)):
            for p in perms:
                if iso(c, t, p):
                    found = (p, flag); break
            if found: break
        assert found, c
        p, flag = found
        code = sum(p[i] << (3 * i) for i in range(6))
        certs.append((c, code, flag))
print("count", len(certs), "prism", sum(1 for x in certs if x[2]))
lines = []
for (c, code, flag) in certs:
    lines.append(f"({c}, {code}, {'true' if flag else 'false'})")
print("[" + ",\n  ".join(lines) + "]")
