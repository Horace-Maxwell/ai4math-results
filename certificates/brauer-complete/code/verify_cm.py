"""Implementation 2 (independent of diagrams.py / construct.py): verify a
complete-mapping certificate for B_n or PB_n directly on diagrams.

Certificate line: "<x>\t<alpha(x)>", each diagram written as space-separated
blocks, 'a:b' for a 2-block and 'a' for a singleton, points 1..n (top) and
1'..n' (bottom).

Product: x on top of y; computed by walking alternating paths through the
middle row (no union-find, no shared code).

Checks for a principal-factor certificate of rank r (factor J_r^0, zero fixed):
  * every key is a valid diagram of the family (B: perfect matching of the
    2n points; PB: partial matching) of rank r, keys pairwise distinct, and
    the number of keys equals |J_r| computed from the closed formula
      B_n : |J_r| = (C(n,r) (n-r-1)!!)^2 r!,   PB_n : (C(n,r) a(n-r))^2 r!
    (a(k) = number of involutions of a k-set);  hence the key set is J_r;
  * the values are valid rank-r diagrams, pairwise distinct (alpha bijective);
  * x * alpha(x) has rank r for every x (never 0 in the factor), and these
    products are pairwise distinct (theta bijective on J_r; theta(0) = 0).
For a whole-monoid certificate: keys = all of the monoid (count = |B_n| or
|PB_n|), alpha bijective, theta bijective.
"""
import sys, hashlib
from math import comb, factorial


def dfact(k):
    r = 1
    while k > 1:
        r *= k
        k -= 2
    return r


def inv_count(k):
    a, b = 1, 1           # a(0), a(1)
    if k == 0:
        return 1
    for j in range(2, k + 1):
        a, b = b, b + (j - 1) * a
    return b


def parse_point(s, n):
    if s.endswith("'"):
        v = int(s[:-1])
        assert 1 <= v <= n
        return ('b', v)
    v = int(s)
    assert 1 <= v <= n
    return ('t', v)


def parse(line_part, n, family):
    """returns frozenset of blocks (each a frozenset of 1 or 2 points)."""
    blocks = []
    seen = set()
    for tok in line_part.split():
        pts = [parse_point(p, n) for p in tok.split(":")]
        assert 1 <= len(pts) <= 2
        for p in pts:
            assert p not in seen, "point used twice"
            seen.add(p)
        blocks.append(frozenset(pts))
    assert len(seen) == 2 * n, "not all points covered"
    if family == "B":
        assert all(len(b) == 2 for b in blocks), "singleton in a Brauer diagram"
    return frozenset(blocks)


def partner_map(d):
    m = {}
    for b in d:
        pts = list(b)
        if len(pts) == 2:
            m[pts[0]] = pts[1]
            m[pts[1]] = pts[0]
    return m


def mult(x, y, n):
    """x on top of y. Middle row: x's bottom points = y's top points."""
    mx = partner_map(x)
    my = partner_map(y)
    # outer points of the product: ('t',i) from x's top, ('b',i) from y's bottom
    def walk(start):
        # start: ('t',i) in x or ('b',i) in y; returns end outer point or None
        if start[0] == 't':
            side = 'x'
            p = start
        else:
            side = 'y'
            p = start
        while True:
            if side == 'x':
                q = mx.get(p)
                if q is None:
                    return None
                if q[0] == 't':
                    return ('t', q[1])            # reached x's top: outer point
                # q = ('b', k) of x = middle point k -> continue in y at ('t',k)
                p = ('t', q[1]); side = 'y'
            else:
                q = my.get(p)
                if q is None:
                    return None
                if q[0] == 'b':
                    return ('b', q[1])            # reached y's bottom: outer point
                # q = ('t', k) of y = middle point k -> continue in x at ('b',k)
                p = ('b', q[1]); side = 'x'
    blocks = set()
    done = set()
    for i in range(1, n + 1):
        for start in (('t', i), ('b', i)):
            if start in done:
                continue
            end = walk(start)
            done.add(start)
            if end is None:
                blocks.add(frozenset([start]))
            else:
                assert end not in done or end == start
                done.add(end)
                blocks.add(frozenset([start, end]))
    return frozenset(blocks)


def rank(d):
    return sum(1 for b in d if len(b) == 2 and {p[0] for p in b} == {'t', 'b'})


def check(path, family, n, r):
    data = open(path, "rb").read()
    sha = hashlib.sha256(data).hexdigest()
    keys, vals = [], []
    for line in data.decode().splitlines():
        if not line or line.startswith("#"):
            continue
        a, b = line.split("\t")
        keys.append(parse(a, n, family))
        vals.append(parse(b, n, family))
    if r == "all":
        expected = dfact(2 * n - 1) if family == "B" else inv_count(2 * n)
    else:
        r = int(r)
        if family == "B":
            assert (n - r) % 2 == 0
            N = comb(n, r) * dfact(n - r - 1)
        else:
            N = comb(n, r) * inv_count(n - r)
        expected = N * N * factorial(r)
    assert len(keys) == expected, (len(keys), expected)
    assert len(set(keys)) == len(keys), "duplicate keys"
    assert len(set(vals)) == len(vals), "alpha not injective"
    if r != "all":
        assert all(rank(k) == r for k in keys), "key of wrong rank"
        assert all(rank(v) == r for v in vals), "value of wrong rank"
    else:
        assert set(vals) == set(keys), "alpha not onto the monoid"
    thetas = set()
    for x, y in zip(keys, vals):
        z = mult(x, y, n)
        if r != "all":
            assert rank(z) == r, "product leaves the J-class (is 0 in the factor)"
        thetas.add(z)
    assert len(thetas) == len(keys), "theta not injective"
    if r == "all":
        assert thetas == set(keys)
    return sha, len(keys)


def selftest():
    # small sanity checks of mult against hand computations
    n = 2
    # identity in B_2: 1:1' 2:2'
    e = parse("1:1' 2:2'", 2, "B")
    s = parse("1:2' 2:1'", 2, "B")
    u = parse("1:2 1':2'", 2, "B")
    assert mult(e, s, 2) == s and mult(s, e, 2) == s and mult(s, s, 2) == e
    assert mult(u, u, 2) == u and mult(u, s, 2) == u and mult(s, u, 2) == u
    assert rank(u) == 0 and rank(s) == 2
    # PB_1
    one = parse("1:1'", 1, "PB"); z = parse("1 1'", 1, "PB")
    assert mult(one, z, 1) == z and mult(z, z, 1) == z
    # B_3 example: x = 1:2 3:1' 2':3' ; y = 1:1' 2:3 2':3'  -> x*y: top 1:2, 3 -> 1' ->(y) 1'?
    x = parse("1:2 3:1' 2':3'", 3, "B")
    y = parse("1:1' 2:3 2':3'", 3, "B")
    # middle: x bottom {2,3} arc, 1 free(from top 3); y top 1 free(to bottom 1'), {2,3} arc -> loop
    assert mult(x, y, 3) == parse("1:2 3:1' 2':3'", 3, "B")
    return True


if __name__ == "__main__":
    selftest()
    path, family, n, r = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
    sha, k = check(path, family, n, r)
    print(f"VERIFIED {path}: family={family} n={n} rank={r} entries={k} sha256={sha}")
