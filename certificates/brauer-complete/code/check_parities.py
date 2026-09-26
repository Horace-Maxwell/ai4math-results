"""Parity table of the index-set sizes N(n,r) for ranks 2 and 3 (exact integers)."""
from math import comb
def dfact(k):
    r = 1
    while k > 1:
        r *= k; k -= 2
    return r
def inv(k):
    a, b = 1, 1
    if k == 0: return 1
    for j in range(2, k + 1):
        a, b = b, b + (j - 1) * a
    return b
bad = []
for n in range(1, 201):
    for r in (2, 3):
        if r > n: continue
        if (n - r) % 2 == 0:
            NB = comb(n, r) * dfact(n - r - 1)
            pred = (r == 2 and n % 4 == 2) or (r == 3 and n % 4 == 3)
            if (NB % 2 == 1) != pred: bad.append(("B", n, r, NB))
        NP = comb(n, r) * inv(n - r)
        predP = (n, r) in [(2, 2), (3, 2), (3, 3)]
        if (NP % 2 == 1) != predP: bad.append(("PB", n, r, NP))
print("mismatches:", bad)
print("B_n odd N (proper, n<=40):", [(n, r, comb(n, r) * dfact(n - r - 1)) for n in range(1, 41) for r in (2, 3) if r < n and (n - r) % 2 == 0 and comb(n, r) * dfact(n - r - 1) % 2])
print("PB_n odd N (n<=200):", [(n, r) for n in range(1, 201) for r in (2, 3) if r <= n and comb(n, r) * inv(n - r) % 2])
