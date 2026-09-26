"""Implementation 2: coordinate-free check of the negative triangle (Lemma D).
With e_I the projection of half-diagram I (top half I, bottom half I, vertical
through strings), the product e_{I0} e_{I1} e_{I2} e_{I0} lies in the group
H-class of e_{I0} (isomorphic to S_r) and must be the element swapping the two
smallest free points (an odd permutation); each partial product must keep rank r."""
from verify_cm import mult, rank, parse

def proj(n, free, arcs):
    blocks = [f"{a}:{a}'" for a in free] + [f"{a}:{b}" for a, b in arcs] + [f"{a}':{b}'" for a, b in arcs]
    return parse(" ".join(blocks), n, "B")

for n, r in [(6, 2), (7, 3), (10, 2), (11, 3)]:
    E = [] if r == 2 else [5]
    start = 5 if r == 2 else 6
    R0 = [(k, k + 1) for k in range(start, n + 1, 2)]
    I0 = proj(n, [3, 4] + E, [(1, 2)] + R0)
    I1 = proj(n, [2, 4] + E, [(1, 3)] + R0)
    I2 = proj(n, [2, 3] + E, [(1, 4)] + R0)
    a = mult(I0, I1, n); assert rank(a) == r
    b = mult(a, I2, n); assert rank(b) == r
    c = mult(b, I0, n); assert rank(c) == r
    expected = parse(" ".join(["3:4'", "4:3'"] + [f"{e}:{e}'" for e in E] + ["1:2", "1':2'"] + [f"{x}:{y}" for x, y in R0] + [f"{x}':{y}'" for x, y in R0]), n, "B")
    assert c == expected, (n, r)
    # and the 'positive' orientation: e_{I0} e_{I1} e_{I0} is e_{I0} itself (even)
    d = mult(mult(I0, I1, n), I0, n)
    assert d == I0
    print(f"n={n} r={r}: e_I0 e_I1 e_I2 e_I0 = transposition of free points 3,4 in the group H-class of e_I0 (odd); e_I0 e_I1 e_I0 = e_I0")
print("TRIANGLE CHECK (implementation 2) PASSED")
