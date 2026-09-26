"""Implementation 1: Brauer monoid B_n and partial Brauer monoid PB_n.

A diagram is a tuple m of length 2n.  Points 0..n-1 are the top points 1..n,
points n..2n-1 are the bottom points 1'..n'.  m[p] = q if {p,q} is a block,
m[p] = -1 if {p} is a singleton block (only in PB_n).

Product x*y: x is drawn above y (standard diagram-monoid convention, as in
East-Mitchell-Ruskuc-Torpey and in arXiv:2608.25092, Sec. 8).
This module computes products with a union-find on 3n points.
"""
from itertools import permutations


# ---------------------------------------------------------------- enumeration
def perfect_matchings(points):
    points = list(points)
    if not points:
        yield []
        return
    a = points[0]
    for k in range(1, len(points)):
        b = points[k]
        rest = points[1:k] + points[k + 1:]
        for m in perfect_matchings(rest):
            yield [(a, b)] + m


def partial_matchings(points):
    points = list(points)
    if not points:
        yield []
        return
    a = points[0]
    rest = points[1:]
    for m in partial_matchings(rest):          # a is a singleton
        yield m
    for k in range(len(rest)):                   # a matched with rest[k]
        b = rest[k]
        rest2 = rest[:k] + rest[k + 1:]
        for m in partial_matchings(rest2):
            yield [(a, b)] + m


def pairs_to_diagram(pairs, size):
    m = [-1] * size
    for a, b in pairs:
        m[a] = b
        m[b] = a
    return tuple(m)


def brauer_elements(n):
    return [pairs_to_diagram(p, 2 * n) for p in perfect_matchings(range(2 * n))]


def partial_brauer_elements(n):
    return [pairs_to_diagram(p, 2 * n) for p in partial_matchings(range(2 * n))]


# -------------------------------------------------------------------- product
class UF:
    def __init__(self, k):
        self.p = list(range(k))

    def find(self, a):
        while self.p[a] != a:
            self.p[a] = self.p[self.p[a]]
            a = self.p[a]
        return a

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.p[ra] = rb


def product(x, y):
    """x*y with x on top.  Nodes: T_i = i, M_i = n+i, B_i = 2n+i."""
    n = len(x) // 2
    uf = UF(3 * n)
    # x: top i -> T_i, bottom i -> M_i
    for p in range(2 * n):
        q = x[p]
        if q > p:
            uf.union(p if p < n else n + (p - n), q if q < n else n + (q - n))
    # y: top i -> M_i, bottom i -> B_i
    for p in range(2 * n):
        q = y[p]
        if q > p:
            uf.union(n + p if p < n else 2 * n + (p - n), n + q if q < n else 2 * n + (q - n))
    outer = list(range(n)) + list(range(2 * n, 3 * n))
    comp = {}
    for v in outer:
        comp.setdefault(uf.find(v), []).append(v)
    m = [-1] * (2 * n)
    for vs in comp.values():
        assert len(vs) <= 2
        if len(vs) == 2:
            a, b = vs
            a2 = a if a < n else a - n
            b2 = b if b < n else b - n
            m[a2] = b2
            m[b2] = a2
    return tuple(m)


def rank(x):
    n = len(x) // 2
    return sum(1 for p in range(n) if x[p] >= n)


# ------------------------------------------------- Rees coordinates (U, g, L)
# A half-diagram is a tuple h of length n: h[i] = 'F' if i is a through point,
# h[i] = j (0 <= j < n) if {i,j} is an arc, h[i] = -1 if i is a singleton.

def upper_half(x):
    n = len(x) // 2
    h = []
    for i in range(n):
        q = x[i]
        if q == -1:
            h.append(-1)
        elif q >= n:
            h.append('F')
        else:
            h.append(q)
    return tuple(h)


def lower_half(x):
    n = len(x) // 2
    h = []
    for i in range(n):
        q = x[n + i]
        if q == -1:
            h.append(-1)
        elif q < n:
            h.append('F')
        else:
            h.append(q - n)
    return tuple(h)


def free_points(h):
    return [i for i, v in enumerate(h) if v == 'F']


def group_part(x):
    """g[k] = index (among sorted bottom through points) of the partner of the
    k-th top through point."""
    n = len(x) // 2
    top = [i for i in range(n) if x[i] >= n]
    bot = [j for j in range(n) if 0 <= x[n + j] < n]
    pos = {j: k for k, j in enumerate(bot)}
    return tuple(pos[x[i] - n] for i in top)


def assemble(U, g, L):
    n = len(U)
    m = [-1] * (2 * n)
    for i, v in enumerate(U):
        if v != 'F' and v != -1:
            m[i] = v
    for j, v in enumerate(L):
        if v != 'F' and v != -1:
            m[n + j] = n + v
    top = free_points(U)
    bot = free_points(L)
    assert len(top) == len(bot) == len(g)
    for k, i in enumerate(top):
        j = bot[g[k]]
        m[i] = n + j
        m[n + j] = i
    return tuple(m)


def projection(h):
    r = len(free_points(h))
    return assemble(h, tuple(range(r)), h)


def compose(a, b):
    """right-action composition: first a then b, (a*b)[k] = b[a[k]]."""
    return tuple(b[a[k]] for k in range(len(a)))


def inverse(a):
    inv = [0] * len(a)
    for k, v in enumerate(a):
        inv[v] = k
    return tuple(inv)


def sign(a):
    a = list(a)
    s = 1
    seen = [False] * len(a)
    for i in range(len(a)):
        if not seen[i]:
            j = i
            L = 0
            while not seen[j]:
                seen[j] = True
                j = a[j]
                L += 1
            if L % 2 == 0:
                s = -s
    return s


def halves(elements, r):
    """all half-diagrams occurring as upper halves of rank-r elements (sorted)."""
    return sorted({upper_half(x) for x in elements if rank(x) == r}, key=repr)


def sandwich(hs):
    """P[lam][i] = g(e_lam * e_i) if rank preserved else None."""
    r = len(free_points(hs[0]))
    P = {}
    for lam in hs:
        el = projection(lam)
        for i in hs:
            z = product(el, projection(i))
            P[(lam, i)] = group_part(z) if rank(z) == r else None
    return P
