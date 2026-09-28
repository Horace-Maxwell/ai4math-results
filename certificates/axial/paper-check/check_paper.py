#!/usr/bin/env python3
"""Exact-arithmetic check of the structure constants, eigenvectors and hand
computations displayed in the paper "A simple primitive axial algebra with a
disconnected non-annihilation graph, and a decomposable axial block"
(all variants of note.tex: examples S, P, E and D).

* Standard library only; all arithmetic is exact (fractions.Fraction).
* The multiplication tables are typed from the text of the paper.  They are
  compared entry by entry with the tables ExS.T, ExE.T, ExD.T and ExP.T of the
  frozen Lean statement file Challenge.lean (version 2).
* Lines marked "(cross-check, not stated in the paper)" test facts that the
  paper does not assert; they are extra consistency checks.
* This program is a cross-check only.  The results of the paper rest on the
  Lean proofs; nothing here is used by them.

Usage:
    python3 check_paper.py [PATH/TO/Challenge.lean]

Without an argument the statement file is looked up relative to this script,
as laid out in the repository:
    certificates/axial/paper-check/check_paper.py
    lean/Research/AxialMSZ/Challenge.lean
Exit code 0 if and only if every check passes.  Each check prints one line.
"""

import hashlib
import re
import sys
from fractions import Fraction as Fr
from itertools import product
from pathlib import Path

DEFAULT_CHALLENGE = (Path(__file__).resolve().parent
                     / "../../../lean/Research/AxialMSZ/Challenge.lean")
FROZEN_V2_SHA256 = "0d88e7321e0f0931f953ea250f2c5dc1d6d5773cd8f78e3080e0d6eeceb13ee1"
CROSS = " (cross-check, not stated in the paper)"

FAILED = []
COUNT = [0]


def check(cond, msg):
    COUNT[0] += 1
    print(("ok   " if cond else "FAIL ") + msg)
    if not cond:
        FAILED.append(msg)


# ---------------------------------------------------------------- linear algebra

def rref(rows):
    """Row-reduced echelon form; returns (rows, pivot columns)."""
    m = [list(r) for r in rows]
    piv = []
    r = 0
    ncols = len(m[0]) if m else 0
    for col in range(ncols):
        p = next((i for i in range(r, len(m)) if m[i][col] != 0), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        inv = 1 / m[r][col]
        m[r] = [v * inv for v in m[r]]
        for i in range(len(m)):
            if i != r and m[i][col] != 0:
                f = m[i][col]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        piv.append(col)
        r += 1
        if r == len(m):
            break
    return m[:r], piv


def rank(rows):
    rows = [r for r in rows]
    if not rows:
        return 0
    return len(rref(rows)[1])


def nullspace(mat):
    """Basis of {v : mat v = 0} (mat given as a list of rows)."""
    n = len(mat[0])
    red, piv = rref(mat)
    free = [j for j in range(n) if j not in piv]
    basis = []
    for f in free:
        v = [Fr(0)] * n
        v[f] = Fr(1)
        for i, p in enumerate(piv):
            v[p] = -red[i][f]
        basis.append(tuple(v))
    return basis


def in_span(v, vecs):
    if all(c == 0 for c in v):
        return True
    if not vecs:
        return False
    return rank(list(vecs) + [v]) == rank(list(vecs))


def det(mat):
    m = [list(r) for r in mat]
    n = len(m)
    d = Fr(1)
    for c in range(n):
        p = next((i for i in range(c, n) if m[i][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            m[c], m[p] = m[p], m[c]
            d = -d
        d *= m[c][c]
        for i in range(c + 1, n):
            f = m[i][c] / m[c][c]
            m[i] = [a - f * b for a, b in zip(m[i], m[c])]
    return d


def dot(u, v):
    return sum(x * y for x, y in zip(u, v))


# ---------------------------------------------------------------- algebras

def V(*xs):
    return tuple(Fr(x) for x in xs)


def add(*vs):
    return tuple(sum(c) for c in zip(*vs))


def sc(s, v):
    return tuple(Fr(s) * c for c in v)


def sub(u, v):
    return add(u, sc(-1, v))


def zero(n):
    return tuple(Fr(0) for _ in range(n))


class Alg:
    def __init__(self, name, T):
        self.name = name
        self.T = T
        self.n = len(T)

    def mul(self, u, v):
        out = [Fr(0)] * self.n
        for i in range(self.n):
            if u[i] == 0:
                continue
            for j in range(self.n):
                if v[j] == 0:
                    continue
                for k in range(self.n):
                    out[k] += u[i] * v[j] * self.T[i][j][k]
        return tuple(out)

    def e(self, i):
        return tuple(Fr(1) if k == i else Fr(0) for k in range(self.n))

    def ad_matrix(self, a):
        """Matrix (rows) of ad_a in the standard basis: column j = a*e_j."""
        cols = [self.mul(a, self.e(j)) for j in range(self.n)]
        return [[cols[j][i] for j in range(self.n)] for i in range(self.n)]

    def eigenspace(self, a, lam):
        M = self.ad_matrix(a)
        for i in range(self.n):
            M[i][i] -= Fr(lam)
        return nullspace(M)

    def commutative(self):
        return all(self.mul(self.e(i), self.e(j)) == self.mul(self.e(j), self.e(i))
                   for i in range(self.n) for j in range(self.n))

    def gen(self, X):
        """Subalgebra generated by X (basis of a subspace)."""
        span = []
        for x in X:
            if not in_span(x, span):
                span.append(x)
        changed = True
        while changed:
            changed = False
            for u in list(span):
                for v in list(span):
                    p = self.mul(u, v)
                    if not in_span(p, span):
                        span.append(p)
                        changed = True
        return span

    def ideal(self, gens):
        """Smallest ideal containing gens."""
        span = []
        for x in gens:
            if not in_span(x, span):
                span.append(x)
        changed = True
        while changed:
            changed = False
            for u in list(span):
                for j in range(self.n):
                    p = self.mul(self.e(j), u)
                    if not in_span(p, span):
                        span.append(p)
                        changed = True
        return span

    def is_ideal_in(self, S, J):
        """J (basis) is an ideal of the subalgebra S (basis): J <= S and S J <= J."""
        return all(in_span(j, S) for j in J) and all(
            in_span(self.mul(s, j), J) for s in S for j in J)

    def is_ideal(self, J):
        return self.is_ideal_in([self.e(i) for i in range(self.n)], J)


# ---------------------------------------------------------------- fusion laws
# Python transcriptions of the if-cascades JPlus, JMild, FD3 in Challenge.lean.

def jplus_star(eta):
    def star(l, m):
        if l == 1:
            return set() if m == 0 else {m}
        if m == 1:
            return set() if l == 0 else {l}
        if l == 0 or m == 0:
            return {Fr(1), Fr(0), eta}
        return {Fr(1), Fr(0)}
    return star


def jmild_star(eta):
    def star(l, m):
        if l == 1:
            return set() if m == 0 else {m}
        if m == 1:
            return set() if l == 0 else {l}
        if l == 0 or m == 0:
            return {Fr(0), eta}
        return {Fr(1), Fr(0)}
    return star


def fd3_star(l, m):
    if l == 0 and m == 0:
        return {Fr(0), Fr(1)}
    if l == 1 and m == 1:
        return {Fr(1)}
    if (l, m) in ((1, 2), (2, 1), (2, 2)):
        return {Fr(2)}
    return set()


def is_seress(carrier, star):
    return 0 in carrier and all(star(Fr(0), l) <= {l} for l in carrier)


def is_symmetric_on_carrier(carrier, star):
    return all(star(l, m) == star(m, l) and star(l, m) <= set(carrier)
               for l in carrier for m in carrier)


def paper_tables():
    """The tables as printed in the paper (row lambda, column mu)."""
    h = Fr(1, 2)
    t = Fr(1, 3)
    E = set()
    tab = {}
    for name, eta, kind in (("J+(1/2)", h, "plus"), ("J+(1/3)", t, "plus"),
                            ("Jo(1/2)", h, "mild"), ("J(1/2)", h, "jordan")):
        one, zer = Fr(1), Fr(0)
        if kind == "plus":
            zz, ze = {one, zer, eta}, {one, zer, eta}
        elif kind == "mild":
            zz, ze = {zer, eta}, {zer, eta}
        else:
            zz, ze = {zer}, {eta}
        tab[name] = {
            (one, one): {one}, (one, zer): E, (one, eta): {eta},
            (zer, one): E, (zer, zer): zz, (zer, eta): ze,
            (eta, one): {eta}, (eta, zer): ze, (eta, eta): {one, zer},
        }
    z, o, w = Fr(0), Fr(1), Fr(2)
    tab["FD3"] = {(l, m): E for l in (z, o, w) for m in (z, o, w)}
    tab["FD3"].update({(z, z): {z, o}, (o, o): {o}, (o, w): {w}, (w, o): {w},
                       (w, w): {w}})
    return tab


def check_fusion_laws():
    print("== fusion laws: printed tables vs. Lean if-cascades; symmetry; Seress")
    tab = paper_tables()
    h, t = Fr(1, 2), Fr(1, 3)
    laws = {"J+(1/2)": ([Fr(1), Fr(0), h], jplus_star(h)),
            "J+(1/3)": ([Fr(1), Fr(0), t], jplus_star(t)),
            "Jo(1/2)": ([Fr(1), Fr(0), h], jmild_star(h)),
            "FD3": ([Fr(0), Fr(1), Fr(2)], fd3_star)}
    for name, (car, star) in laws.items():
        same = all(star(l, m) == tab[name][(l, m)] for l in car for m in car)
        check(same, f"{name}: printed table = Lean if-cascade on carrier x carrier")
        check(is_symmetric_on_carrier(car, star),
              f"{name}: symmetric, values in the carrier (on carrier x carrier)")
    for name in ("J+(1/2)", "J+(1/3)", "Jo(1/2)"):
        car, star = laws[name]
        check(not is_seress(car, star), f"{name}: not Seress")
    check(Fr(1) in jplus_star(h)(Fr(0), Fr(0)), "J+(1/2): 1 in 0*0")
    check(h in jmild_star(h)(Fr(0), Fr(0)), "Jo(1/2): 1/2 in 0*0")
    diff = [k for k in tab["J(1/2)"] if tab["J(1/2)"][k] != tab["J+(1/2)"][k]]
    check(sorted(diff) == sorted([(Fr(0), Fr(0)), (Fr(0), h), (h, Fr(0))]),
          "J+(1/2) differs from J(1/2) exactly at 0*0, 0*1/2, 1/2*0")
    diff = [k for k in tab["J(1/2)"] if tab["J(1/2)"][k] != tab["Jo(1/2)"][k]]
    check(sorted(diff) == sorted([(Fr(0), Fr(0)), (Fr(0), h), (h, Fr(0))]),
          "Jo(1/2) differs from J(1/2) exactly at 0*0, 0*1/2, 1/2*0")
    return laws


# ---------------------------------------------------------------- Lean tables

def parse_lean_table(src, ns):
    m = re.search(r"namespace %s\b.*?def T\b[^\n]*\n(.*?)\n\n" % ns, src, re.S)
    body = m.group(1)
    inner = re.findall(r"!\[([^\[\]]*)\]", body)
    vecs = [tuple(Fr(x.strip()) for x in s.split(",")) for s in inner]
    n = len(vecs[0])
    assert len(vecs) == n * n, (ns, len(vecs))
    return [[vecs[i * n + j] for j in range(n)] for i in range(n)]


# ---------------------------------------------------------------- the algebras
# Tables typed from the text of the paper, NOT read from Lean.

def matsuo_block(eta, n):
    """Products of a=e0, b=e1, x=e2 in 3C(eta) inside an n-dim space."""
    a, b, x = (tuple(Fr(1) if k == i else Fr(0) for k in range(n)) for i in range(3))
    k = Fr(eta) / 2
    return {(0, 0): a, (1, 1): b, (2, 2): x,
            (0, 1): sc(k, sub(add(a, b), x)),
            (0, 2): sc(k, sub(add(a, x), b)),
            (1, 2): sc(k, sub(add(b, x), a))}


def build(n, prods):
    T = [[zero(n) for _ in range(n)] for _ in range(n)]
    for (i, j), v in prods.items():
        T[i][j] = v
        T[j][i] = v
    return T


def algebra_S():
    n = 4
    p = matsuo_block(Fr(1, 2), n)
    a, b, x, c = (tuple(Fr(1) if k == i else Fr(0) for k in range(n)) for i in range(n))
    p[(3, 3)] = c
    p[(2, 3)] = sub(sc(Fr(1, 2), sub(sub(x, a), b)), sc(Fr(1, 4), c))  # cx
    return Alg("S", build(n, p))


def algebra_E():
    n = 4
    p = matsuo_block(Fr(1, 3), n)
    a, b, x, c = (tuple(Fr(1) if k == i else Fr(0) for k in range(n)) for i in range(n))
    p[(3, 3)] = c
    p[(2, 3)] = sc(Fr(1, 3), sub(sub(x, a), b))  # cx
    return Alg("E", build(n, p))


def algebra_D():
    n = 5
    p = matsuo_block(Fr(1, 2), n)
    a, b, x, c, d = (tuple(Fr(1) if k == i else Fr(0) for k in range(n)) for i in range(n))
    p[(3, 3)] = c
    p[(2, 3)] = d                    # cx = d
    p[(3, 4)] = sc(Fr(1, 2), d)      # cd = d/2
    return Alg("D", build(n, p))


def algebra_P():
    n = 2
    a, b = (tuple(Fr(1) if k == i else Fr(0) for k in range(n)) for i in range(n))
    p = {(0, 0): a, (0, 1): sc(2, b), (1, 1): b}
    return Alg("P", build(n, p))


# ---------------------------------------------------------------- generic axis check

def fmt(v):
    return "(" + ",".join(str(c) for c in v) + ")"


def check_axis(A, s, carrier, star, eig, label):
    """eig: dict lambda -> list of vectors claimed to span A_lambda(s)."""
    n = A.n
    check(A.mul(s, s) == s and any(s), f"{label}: non-zero idempotent")
    for lam, vs in eig.items():
        for v in vs:
            check(A.mul(s, v) == sc(lam, v), f"{label}: {fmt(v)} in A_{lam}")
    allv = [v for vs in eig.values() for v in vs]
    check(len(allv) == n and rank(allv) == n, f"{label}: the listed eigenvectors form a basis")
    for lam in carrier:
        dim = len(A.eigenspace(s, lam))
        check(dim == len(eig.get(lam, [])), f"{label}: dim A_{lam} = {dim} (as listed)")
    one = eig.get(Fr(1), [])
    check(len(one) == 1 and in_span(s, one), f"{label}: A_1 = <axis> (primitive)")
    ok = True
    for l in carrier:
        for m in carrier:
            target = [v for mu in star(l, m) for v in eig.get(mu, [])]
            for u in eig.get(l, []):
                for v in eig.get(m, []):
                    if not in_span(A.mul(u, v), target):
                        ok = False
                        print(f"     fusion fails: {label} {l}*{m} {fmt(u)} {fmt(v)}")
    check(ok, f"{label}: A_l A_m in A_(l*m) for all l, m in F (all eigenbasis pairs)")


# ---------------------------------------------------------------- S

def check_S(laws, lean):
    print("== Example S (Theorem A)")
    S = algebra_S()
    check(S.T == lean["ExS"], "S: table from the paper = ExS.T in Challenge.lean")
    check(S.commutative(), "S: commutative")
    a, b, x, c = (S.e(i) for i in range(4))
    m = S.mul
    h = Fr(1, 2)
    q = Fr(1, 4)
    check(m(a, b) == sc(q, sub(add(a, b), x)), "S: ab = (a+b-x)/4")
    check(m(a, x) == sc(q, sub(add(a, x), b)), "S: ax = (a-b+x)/4")
    check(m(b, x) == sc(q, sub(add(b, x), a)), "S: bx = (-a+b+x)/4")
    check(m(x, c) == sub(sc(h, sub(sub(x, a), b)), sc(q, c)), "S: cx = (-a-b+x)/2 - c/4")
    check(m(a, c) == zero(4) and m(b, c) == zero(4), "S: ac = bc = 0")
    car, star = laws["J+(1/2)"]
    za = sub(add(b, x), sc(h, a))
    zb = sub(add(a, x), sc(h, b))
    w = add(sc(2, sub(sub(x, a), b)), c)
    check_axis(S, a, car, star, {Fr(1): [a], Fr(0): [za, c], h: [sub(x, b)]},
               "S axis a: A_0 = <b+x-a/2, c>, A_1/2 = <x-b>")
    check_axis(S, b, car, star, {Fr(1): [b], Fr(0): [zb, c], h: [sub(x, a)]},
               "S axis b: A_0 = <a+x-b/2, c>, A_1/2 = <x-a>")
    check_axis(S, c, car, star, {Fr(1): [c], Fr(0): [a, b], h: [w]},
               "S axis c: A_0 = <a, b>, A_1/2 = <w>, w = 2(x-a-b)+c")
    check(m(a, za) == zero(4) and add(sc(q, sub(add(a, b), x)), sc(q, sub(add(a, x), b)),
                                      sc(-h, a)) == zero(4),
          "S: a(b+x-a/2) = (a+b-x)/4 + (a-b+x)/4 - a/2 = 0")
    check(m(a, sub(x, b)) == sc(h, sub(x, b)), "S: a(x-b) = (x-b)/2")
    check(add(sc(2, m(c, x)), c) == add(sub(sub(x, a), b), sc(h, c)) == sc(h, w) == m(c, w),
          "S: cw = 2cx + c = (x-a-b) + c/2 = w/2")
    xb, xa = sub(x, b), sub(x, a)
    check(m(xb, xb) == add(sc(Fr(3, 4), a), sc(h, za)), "S: (x-b)^2 = 3a/4 + (b+x-a/2)/2")
    check(m(xa, xa) == add(sc(Fr(3, 4), b), sc(h, zb)), "S: (x-a)^2 = 3b/4 + (a+x-b/2)/2")
    check(m(w, w) == sc(4, add(a, b)), "S: w^2 = 4a + 4b")
    check(x == sub(add(a, b), sc(4, m(a, b))), "S: x = a + b - 4ab")
    check(len(S.gen([a, b, c])) == 4, "S: <<a,b,c>> = S")
    check(len(S.gen([a, b])) == 3 and len(S.gen([c])) == 1,
          "S: <<a,b>> = <a,b,x> and <<c>> = <c>")
    check(m(a, b) != zero(4) and m(a, c) == zero(4) and m(b, c) == zero(4),
          "S: Delta(X) has the single edge a-b")
    check(m(x, c) != zero(4), "S: xc != 0, so <<a,b>> and <<c>> do not annihilate each other")
    # simplicity: the projection P_c and the four linear forms
    al, be, xi, ga = (Fr(k) for k in (3, -5, 7, 11))
    u = V(al, be, xi, ga)
    dec = add(sc(al + xi, a), sc(be + xi, b), sc(xi / 2, w), sc(ga - xi / 2, c))
    check(dec == u, "S: u = (alpha+xi)a + (beta+xi)b + (xi/2)w + (gamma-xi/2)c")
    Pc = lambda v: sub(sc(2, m(c, m(c, v))), m(c, v))
    phi = lambda v: v[3] - v[2] / 2
    check(all(Pc(S.e(i)) == sc(phi(S.e(i)), c) for i in range(4)),
          "S: P_c = 2 ad_c^2 - ad_c satisfies P_c(u) = phi(u) c with phi(u) = gamma - xi/2")
    rows = []
    for f in (lambda v: v, lambda v: m(a, v), lambda v: m(b, v), lambda v: m(x, v)):
        rows.append(tuple(phi(f(S.e(i))) for i in range(4)))
    exp = [V(0, 0, -h, 1), V(0, Fr(1, 8), -Fr(1, 8), 0), V(Fr(1, 8), 0, -Fr(1, 8), 0),
           V(-Fr(1, 8), -Fr(1, 8), -h, -h)]
    check(rows == exp,
          "S: coefficient vectors of phi(u), phi(au), phi(bu), phi(xu) as printed")
    # the direct solution printed in the paper
    check(rows[1] == sc(Fr(1, 8), V(0, 1, -1, 0)),
          "S: phi(au) = (beta - xi)/8, so phi(au) = 0 gives beta = xi")
    check(rows[2] == sc(Fr(1, 8), V(1, 0, -1, 0)),
          "S: phi(bu) = (alpha - xi)/8, so phi(bu) = 0 gives alpha = xi")
    check(rows[0] == V(0, 0, -h, 1), "S: phi(u) = gamma - xi/2, so phi(u) = 0 gives gamma = xi/2")
    ker3 = nullspace([rows[1], rows[2], rows[0]])
    check(len(ker3) == 1 and in_span(V(1, 1, 1, h), ker3),
          "S: phi(u) = phi(au) = phi(bu) = 0 iff (alpha,beta,xi,gamma) = xi(1,1,1,1/2)")
    check(dot(rows[3], V(1, 1, 1, h)) == -1,
          "S: at such u, phi(xu) = -xi; so all four vanish only at u = 0")
    check(det(rows) == Fr(-1, 64), "S: determinant of the four vectors = -1/64" + CROSS)
    xc = m(x, c)
    check(xc == V(-h, -h, h, -q), "S: xc = -a/2 - b/2 + x/2 - c/4")
    axc, bxc = m(a, xc), m(b, xc)
    check(axc == V(-h, -q, q, 0), "S: a(xc) = -a/2 - b/4 + x/4")
    check(bxc == V(-q, -h, q, 0), "S: b(xc) = -a/4 - b/2 + x/4")
    check(add(sc(h, c), sc(2, xc), sc(-4, axc)) == a, "S: a = c/2 + 2xc - 4a(xc)")
    check(add(sc(h, c), sc(2, xc), sc(-4, bxc)) == b, "S: b = c/2 + 2xc - 4b(xc)")
    check(m(c, c) == c and c != zero(4), "S: c^2 = c != 0, so S^2 != 0")
    # cross-checks
    swap = lambda v: (v[1], v[0], v[2], v[3])
    check(all(swap(m(S.e(i), S.e(j))) == m(swap(S.e(i)), swap(S.e(j)))
              for i in range(4) for j in range(4)),
          "S: exchanging a and b (fixing x, c) is an automorphism" + CROSS)
    mats = [S.ad_matrix(S.e(i)) for i in range(4)]
    flat = lambda M: tuple(M[i][j] for i in range(4) for j in range(4))
    span = []
    for M in mats:
        if not in_span(flat(M), span):
            span.append(flat(M))
    words = mats[:]
    for _ in range(3):
        new = []
        for M in words:
            for N in mats:
                PM = [[sum(M[i][k] * N[k][j] for k in range(4)) for j in range(4)]
                      for i in range(4)]
                if not in_span(flat(PM), span):
                    span.append(flat(PM))
                    new.append(PM)
        words = new
    check(len(span) == 16, "S: the multiplication algebra has dimension 16" + CROSS)
    for v in (a, b, x, c, V(1, -1, 0, 0), V(0, 0, 1, 2), V(2, 2, -1, 1)):
        check(len(S.ideal([v])) == 4, f"S: the ideal generated by {fmt(v)} is S" + CROSS)


# ---------------------------------------------------------------- P

def check_P(laws, lean):
    print("== Example P (Proposition on Peng's algebra)")
    P = algebra_P()
    check(P.T == lean["ExP"], "P: table from the paper = ExP.T in Challenge.lean")
    check(P.commutative(), "P: commutative")
    a, b = P.e(0), P.e(1)
    car, star = laws["FD3"]
    z = sub(a, sc(2, b))
    check_axis(P, a, car, star, {Fr(1): [a], Fr(2): [b]}, "P axis a: A_1 = <a>, A_2 = <b>")
    check_axis(P, b, car, star, {Fr(1): [b], Fr(0): [z]}, "P axis b: A_1 = <b>, A_0 = <a-2b>")
    check(P.mul(b, b) == b, "P: b^2 = b, in A_2(a)")
    check(P.mul(z, z) == sub(a, sc(4, b)) == sub(z, sc(2, b)),
          "P: (a-2b)^2 = a - 4b = (a-2b) - 2b")
    check(P.mul(b, z) == zero(2), "P: b(a-2b) = 0")
    check(len(P.gen([a, b])) == 2, "P: a and b span P")
    check(P.is_ideal([b]), "P: <b> is an ideal")
    check(P.mul(a, a) == a and P.mul(a, b) == sc(2, b), "P: ab = 2b")
    Ib, Ia = P.ideal([b]), P.ideal([a])
    check(len(Ib) == 1 and in_span(b, Ib) and len(Ia) == 2, "P: I_b = <b> and I_a = P")


# ---------------------------------------------------------------- D

def check_D(laws, lean):
    print("== Example D (Theorem C)")
    D = algebra_D()
    check(D.T == lean["ExD"], "D: table from the paper = ExD.T in Challenge.lean")
    check(D.commutative(), "D: commutative")
    a, b, x, c, d = (D.e(i) for i in range(5))
    m = D.mul
    h = Fr(1, 2)
    q = Fr(1, 4)
    check(all(m(d, v) == zero(5) for v in (a, b, x, d)), "D: ad = bd = xd = d^2 = 0")
    check(m(c, c) == c and m(c, a) == zero(5) and m(c, b) == zero(5) and m(c, x) == d
          and m(c, d) == sc(h, d), "D: c^2 = c, ac = bc = 0, cx = d, cd = d/2")
    car, star = laws["Jo(1/2)"]
    za = sub(add(b, x), sc(h, a))
    zb = sub(add(a, x), sc(h, b))
    x2d = sub(x, sc(2, d))
    check_axis(D, a, car, star, {Fr(1): [a], Fr(0): [za, c, d], h: [sub(x, b)]},
               "D axis a: A_0 = <b+x-a/2, c, d>, A_1/2 = <x-b>")
    check_axis(D, b, car, star, {Fr(1): [b], Fr(0): [zb, c, d], h: [sub(x, a)]},
               "D axis b: A_0 = <a+x-b/2, c, d>, A_1/2 = <x-a>")
    check_axis(D, c, car, star, {Fr(1): [c], Fr(0): [a, b, x2d], h: [d]},
               "D axis c: A_0 = <a, b, x-2d>, A_1/2 = <d>")
    check(m(za, c) == d and m(sub(x, b), c) == d and m(a, d) == zero(5),
          "D: (b+x-a/2)c = (x-b)c = d, and d is in A_0(a)")
    check(m(zb, c) == d and m(sub(x, a), c) == d and m(b, d) == zero(5),
          "D: (a+x-b/2)c = (x-a)c = d, and d is in A_0(b)")
    check(m(za, za) == sc(Fr(3, 2), za) and m(za, sub(x, b)) == sc(Fr(3, 4), sub(x, b)),
          "D: in 3C(1/2), (b+x-a/2)^2 = (3/2)(b+x-a/2) and (b+x-a/2)(x-b) = (3/4)(x-b)"
          + CROSS)
    check(m(a, b) == sub(sc(q, sub(add(a, b), x2d)), sc(h, d)),
          "D: ab = (a+b-(x-2d))/4 - d/2")
    check(m(a, x2d) == add(sc(q, add(sub(a, b), x2d)), sc(h, d)),
          "D: a(x-2d) = (a-b+(x-2d))/4 + d/2")
    check(m(b, x2d) == add(sc(q, add(sub(b, a), x2d)), sc(h, d)),
          "D: b(x-2d) = (-a+b+(x-2d))/4 + d/2")
    check(m(x2d, x2d) == x == add(x2d, sc(2, d)), "D: (x-2d)^2 = (x-2d) + 2d")
    check(m(x2d, d) == zero(5) and m(a, d) == zero(5) and m(b, d) == zero(5)
          and m(d, d) == zero(5), "D: a, b, x-2d and d annihilate d")
    check(x == sub(add(a, b), sc(4, m(a, b))) and d == m(c, x), "D: x = a+b-4ab and d = cx")
    check(len(D.gen([a, b, c])) == 5, "D: <<a,b,c>> = D")
    Iab = [a, b, x, d]
    check(D.is_ideal(Iab), "D: <a,b,x,d> is an ideal of D")
    check(sub(m(a, b), m(a, x)) == sc(h, sub(b, x)), "D: ab - ax = (b-x)/2")
    bx_ = sub(b, x)
    check(sub(sub(m(b, bx_), sc(q, a)), sc(q, bx_)) == sc(h, b),
          "D: b(b-x) - a/4 - (b-x)/4 = b/2")
    Ia = D.ideal([a])
    check(len(Ia) == 4 and all(in_span(v, Ia) for v in Iab), "D: I_a = <a,b,x,d>")
    J1, J2 = [a, b, x], [d]
    check(D.is_ideal_in(Iab, J1), "D: <a,b,x> is an ideal of the algebra I_a")
    check(D.is_ideal_in(Iab, J2), "D: <d> is an ideal of the algebra I_a")
    check(rank(J1) == 3 and rank(J2) == 1 and rank(J1 + J2) == 4,
          "D: both are proper in I_a, and <a,b,x> + <d> = I_a")
    check(not D.is_ideal(J1) and not in_span(m(c, x), J1),
          "D: <a,b,x> is not an ideal of D (cx = d)")
    check(not in_span(c, Iab) and in_span(a, Iab) and in_span(b, Iab),
          "D: X meets I_a in {a, b} (c-coordinate of I_a is 0)")
    gab = D.gen([a, b])
    check(len(gab) == 3 and all(in_span(v, gab) for v in J1),
          "D: <<a,b>> = <a,b,x>, a proper subspace of I_a")
    qq = Fr(1, 4)
    G = [[1, qq, qq, 0, 0], [qq, 1, qq, 0, 0], [qq, qq, 1, 0, 0],
         [0, 0, 0, 1, 0], [0, 0, 0, 0, 0]]
    G = [[Fr(v) for v in r] for r in G]
    beta = lambda u, v: sum(u[i] * G[i][j] * v[j] for i in range(5) for j in range(5))
    check(all(beta(m(D.e(i), D.e(j)), D.e(k)) == beta(D.e(i), m(D.e(j), D.e(k)))
              for i, j, k in product(range(5), repeat=3)),
          "D: beta(uv,w) = beta(u,vw) for all 125 triples of basis vectors")
    check(beta(a, a) == beta(b, b) == beta(c, c) == 1, "D: beta(a,a) = beta(b,b) = beta(c,c) = 1")
    check(beta(a, b) == beta(a, x) == beta(b, x) == qq and beta(x, x) == 1,
          "D: on <a,b,x>, beta is the Matsuo form ((y,y) = 1, (y,z) = 1/4)")
    check(all(beta(d, v) == 0 for v in (a, b, x, c, d)),
          "D: d is orthogonal to D, so beta is degenerate" + CROSS)
    Ib = D.ideal([b])
    check(len(Ib) == 4 and all(in_span(v, Ib) for v in Iab), "D: I_b = <a,b,x,d>" + CROSS)
    swapD = lambda v: (v[1], v[0], v[2], v[3], v[4])
    check(all(swapD(m(D.e(i), D.e(j))) == m(swapD(D.e(i)), swapD(D.e(j)))
              for i in range(5) for j in range(5)),
          "D: exchanging a and b is an automorphism" + CROSS)


# ---------------------------------------------------------------- E

def check_E(laws, lean):
    print("== Example E (Theorem B)")
    E = algebra_E()
    check(E.T == lean["ExE"], "E: table from the paper = ExE.T in Challenge.lean")
    check(E.commutative(), "E: commutative")
    a, b, x, c = (E.e(i) for i in range(4))
    m = E.mul
    t = Fr(1, 3)
    s6 = Fr(1, 6)
    check(m(a, b) == sc(s6, sub(add(a, b), x)) and m(a, x) == sc(s6, sub(add(a, x), b))
          and m(b, x) == sc(s6, sub(add(b, x), a)), "E: ab, ax, bx as printed (3C(1/3))")
    check(m(c, c) == c and m(a, c) == zero(4) and m(b, c) == zero(4)
          and m(c, x) == sc(t, sub(sub(x, a), b)), "E: c^2 = c, ac = bc = 0, cx = (x-a-b)/3")
    car, star = laws["J+(1/3)"]
    za = sub(add(b, x), sc(t, a))
    zb = sub(add(a, x), sc(t, b))
    v = sub(sub(x, a), b)
    check_axis(E, a, car, star, {Fr(1): [a], Fr(0): [za, c], t: [sub(x, b)]},
               "E axis a: A_0 = <b+x-a/3, c>, A_1/3 = <x-b>")
    check_axis(E, b, car, star, {Fr(1): [b], Fr(0): [zb, c], t: [sub(x, a)]},
               "E axis b: A_0 = <a+x-b/3, c>, A_1/3 = <x-a>")
    check_axis(E, c, car, star, {Fr(1): [c], Fr(0): [a, b], t: [v]},
               "E axis c: A_0 = <a, b>, A_1/3 = <v>, v = x-a-b")
    xb, xa = sub(x, b), sub(x, a)
    check(m(xb, xb) == add(sc(Fr(2, 3), za), sc(Fr(5, 9), a)),
          "E: (x-b)^2 = (2/3)(b+x-a/3) + (5/9)a")
    check(m(xa, xa) == add(sc(Fr(2, 3), zb), sc(Fr(5, 9), b)),
          "E: (x-a)^2 = (2/3)(a+x-b/3) + (5/9)b")
    check(m(c, v) == sc(t, v), "E: cv = v/3")
    check(m(v, v) == sc(Fr(4, 3), add(a, b)), "E: v^2 = (4/3)(a+b)")
    check(x == sub(add(a, b), sc(6, m(a, b))), "E: x = a + b - 6ab")
    check(len(E.gen([a, b, c])) == 4, "E: <<a,b,c>> = E")
    W = [a, b, x]
    check(E.is_ideal(W) and in_span(m(c, x), [v]) and m(c, a) == zero(4)
          and m(c, b) == zero(4), "E: W = <a,b,x> is an ideal, since cW is in <v>")
    ab = m(a, b)
    check(sub(sc(9, m(b, ab)), sc(3, ab)) == b, "E: b = 9b(ab) - 3ab")
    check(sub(sc(9, m(a, ab)), sc(3, ab)) == a, "E: a = 9a(ab) - 3ab")
    check(sc(3, m(c, x)) == v, "E: v = 3cx")
    check(m(x, v) == sc(Fr(2, 3), x), "E: xv = (2/3)x")
    check(sub(x, v) == add(a, b), "E: a + b = x - v")
    check(sub(sc(6, m(a, x)), x) == sub(a, b), "E: a - b = 6ax - x")
    Ia, Ib, Ic = E.ideal([a]), E.ideal([b]), E.ideal([c])
    check(len(Ic) == 4, "E: I_c = E")
    check(len(Ia) == 3 and len(Ib) == 3 and all(in_span(u, Ia) and in_span(u, Ib) for u in W),
          "E: I_a = I_b = <a,b,x>, strictly inside I_c = E")
    Pc = lambda u: sc(Fr(1, 2), sub(sc(3, m(c, m(c, u))), m(c, u)))
    check(all(Pc(E.e(i)) == sc(E.e(i)[3], c) for i in range(4)),
          "E: (3 ad_c^2 - ad_c)/2 sends u = alpha a + beta b + xi x + gamma c to gamma c")
    check(m(a, b) != zero(4) and m(a, c) == zero(4) and m(b, c) == zero(4),
          "E: Delta(X) has the single edge a-b")
    check(m(x, c) != zero(4), "E: xc = (x-a-b)/3 != 0")
    swapE = lambda u: (u[1], u[0], u[2], u[3])
    check(all(swapE(m(E.e(i), E.e(j))) == m(swapE(E.e(i)), swapE(E.e(j)))
              for i in range(4) for j in range(4)),
          "E: exchanging a and b is an automorphism" + CROSS)


def main():
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_CHALLENGE
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    print(f"input: {path.name}, SHA-256 {digest}")
    check(digest == FROZEN_V2_SHA256,
          "Challenge.lean is the frozen version 2 (SHA-256 0d88e732...3ee1)")
    src = data.decode("utf-8")
    lean = {ns: parse_lean_table(src, ns) for ns in ("ExS", "ExE", "ExD", "ExP")}
    laws = check_fusion_laws()
    check_S(laws, lean)
    check_P(laws, lean)
    check_D(laws, lean)
    check_E(laws, lean)
    print(f"== {COUNT[0]} checks, {len(FAILED)} failed")
    sys.exit(1 if FAILED else 0)


if __name__ == "__main__":
    main()
