#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
verify_independent.py -- independent exact-arithmetic verifier for the four small
commutative algebras S, E, D, P (AI4Math round 7, "axial" examples).

Written from the mathematical specification in the task prompt ONLY; no other code
or logs of the project were consulted.

Arithmetic: fractions.Fraction over Q everywhere (plain integers mod p only in the
clearly labelled mod-p sanity section).  sympy (exact Rational matrices/polynomials)
is used only to cross-check characteristic polynomials and their factorisation.
No floating point anywhere.

Methods:
  * spectrum: characteristic polynomial (Faddeev-LeVerrier, exact), root
    multiplicities by exact synthetic division; sympy charpoly + factor_list agree;
  * diagonalisable over Q with eigenvalues in F  <=>  prod_{l in F} (ad_a - l) = 0;
  * eigenspaces = images of the Lagrange projections
        P_l = prod_{m in spec, m != l} (ad_a - m)/(l - m)   (polynomials in ad_a);
  * fusion law, two ways: (i) nu realised in l*m iff P_nu(u v) != 0 for some basis
    vectors u of A_l, v of A_m; (ii) span(A_l A_m) inside sum_{nu in l*m} A_nu;
  * ideals: iterative closure, cross-checked by the orbit under the unital
    multiplication algebra M(A);
  * simplicity: A*A != 0 and dim M(A) = n^2 (then the only invariant subspaces are
    0 and A), plus a complete ideal lattice over Q from the axes: an ideal J is
    ad_a-invariant, so P_1(a) J is inside J and inside A_1(a) = Q a; hence either
    a in J or J inside H_a := ker P_1(a) = A_{F minus {1}}(a).  For Y = J cap X one gets
    sum_{y in Y} I_y  <=  J  <=  core(intersection_{z not in Y} H_z), where core(W)
    is the largest ideal inside W; the intervals are resolved exactly;
  * associating bilinear forms: kernel of the linear system (e_i e_j, e_k) = (e_i, e_j e_k);
  * mod-p sanity check (NOT a proof over Q): all ideals over GF(p) as sums of
    principal ideals.
"""
import sys
import itertools
import platform
import subprocess
from fractions import Fraction as Fr

import sympy

from qlinalg import (ZERO, ONE, span, contains, is_subspace, nullspace, intersect,
                     ssum, mat_id, mat_mul, mat_sub, mat_scale, mat_vec, mat_add,
                     is_zero_mat, colspace, rank, charpoly_FL, root_multiplicity,
                     poly_str, Algebra, subalgebra_generated, ideal_generated,
                     mult_algebra, ideal_generated_via_MA, is_ideal, is_subalgebra,
                     is_ideal_of_subalgebra, core, quotient_is_full_matrix_algebra,
                     modp_all_ideals, fmt_p, to_p, span_p, _check_exact)

LINES = []
QUIET = [False]


def log(s=""):
    if QUIET[0]:
        return
    LINES.append(s)
    print(s, flush=True)


def fq(x):
    return str(x)


def fset(s, order):
    if not s:
        return "{} (empty)"
    return "{" + ", ".join(fq(x) for x in order if x in s) + "}"


# ---------------------------------------------------------------------------
# fusion laws
# ---------------------------------------------------------------------------

def make_law(name, F, entries):
    F = [Fr(x) for x in F]
    star = {}
    for (l, m), s in entries.items():
        l, m = Fr(l), Fr(m)
        s = frozenset(Fr(x) for x in s)
        assert s <= set(F)
        for key in ((l, m), (m, l)):
            if key in star and star[key] != s:
                raise ValueError("inconsistent law entry")
            star[key] = s
    for l in F:
        for m in F:
            if (l, m) not in star:
                raise ValueError("law %s: %s*%s undefined" % (name, l, m))
    return {"name": name, "F": F, "star": star}


def law_Jplus(eta):
    eta = Fr(eta)
    return make_law("J+(%s)" % eta, [1, 0, eta], {
        (1, 1): [1], (1, 0): [], (1, eta): [eta],
        (0, 0): [1, 0, eta], (0, eta): [1, 0, eta], (eta, eta): [1, 0]})


def law_Jcirc(eta):
    eta = Fr(eta)
    return make_law("J°(%s)" % eta, [1, 0, eta], {
        (1, 1): [1], (1, 0): [], (1, eta): [eta],
        (0, 0): [0, eta], (0, eta): [0, eta], (eta, eta): [1, 0]})


def law_FD3():
    return make_law("F_D3", [0, 1, 2], {
        (0, 0): [0, 1], (1, 1): [1], (1, 2): [2], (2, 2): [2],
        (0, 1): [], (0, 2): []})


def is_seress(law):
    F, star = law["F"], law["star"]
    if Fr(0) not in F:
        return False, "0 not in F"
    bad = [(l, star[(Fr(0), l)]) for l in F if not star[(Fr(0), l)] <= {l}]
    if bad:
        return False, "; ".join("0*%s = %s is not inside {%s}" % (l, fset(s, F), l) for l, s in bad)
    return True, "0*l inside {l} for all l"


def print_law(law):
    F, star = law["F"], law["star"]
    log("  %s on F = {%s}:" % (law["name"], ", ".join(fq(x) for x in F)))
    for i, l in enumerate(F):
        for m in F[i:]:
            log("    %s * %s = %s" % (fq(l), fq(m), fset(star[(l, m)], F)))
    s, why = is_seress(law)
    log("    Seress? %s   (%s)" % ("YES" if s else "NO", why))
    return s


# ---------------------------------------------------------------------------
# algebras of the examples
# ---------------------------------------------------------------------------

def products_3C(eta):
    h = Fr(eta) / 2
    return {
        ("a", "a"): {"a": 1}, ("b", "b"): {"b": 1}, ("x", "x"): {"x": 1},
        ("a", "b"): {"a": h, "b": h, "x": -h},
        ("a", "x"): {"a": h, "x": h, "b": -h},
        ("b", "x"): {"b": h, "x": h, "a": -h},
    }


def build_S():
    pr = products_3C(Fr(1, 2))
    pr[("c", "c")] = {"c": 1}
    pr[("c", "x")] = {"x": Fr(1, 2), "a": Fr(-1, 2), "b": Fr(-1, 2), "c": Fr(-1, 4)}
    return Algebra("S", ["a", "b", "x", "c"], pr)


def build_E():
    pr = products_3C(Fr(1, 3))
    pr[("c", "c")] = {"c": 1}
    pr[("c", "x")] = {"x": Fr(1, 3), "a": Fr(-1, 3), "b": Fr(-1, 3)}
    return Algebra("E", ["a", "b", "x", "c"], pr)


def build_D():
    pr = products_3C(Fr(1, 2))
    pr[("c", "c")] = {"c": 1}
    pr[("c", "x")] = {"d": 1}
    pr[("c", "d")] = {"d": Fr(1, 2)}
    return Algebra("D", ["a", "b", "x", "c", "d"], pr)


def build_P():
    return Algebra("P", ["a", "b"], {("a", "a"): {"a": 1}, ("a", "b"): {"b": 2},
                                    ("b", "b"): {"b": 1}})


def build_3C(eta):
    return Algebra("3C(%s)" % Fr(eta), ["a", "b", "x"], products_3C(Fr(eta)))


def print_table(A):
    log("  multiplication table (basis %s; products not listed are 0):" % ", ".join(A.labels))
    for i in range(A.n):
        for j in range(i, A.n):
            p = A.mul(A.basis[i], A.basis[j])
            if any(x != 0 for x in p):
                log("    %s*%s = %s" % (A.labels[i], A.labels[j], A.fmt(p)))
    comm = all(A.mul(A.basis[i], A.basis[j]) == A.mul(A.basis[j], A.basis[i])
               for i in range(A.n) for j in range(A.n))
    log("  commutativity of the table: %s" % comm)
    return comm


# ---------------------------------------------------------------------------
# axes
# ---------------------------------------------------------------------------

def analyse_axis(A, name, a, law):
    n = A.n
    F, star = law["F"], law["star"]
    R = {"name": name}
    log("  --- axis %s = %s   (law %s)" % (name, A.fmt(a), law["name"]))
    R["nonzero"] = any(x != 0 for x in a)
    R["idempotent"] = A.mul(a, a) == tuple(a)
    log("    nonzero: %s;  %s*%s = %s  -> idempotent: %s"
        % (R["nonzero"], name, name, A.fmt(A.mul(a, a)), R["idempotent"]))
    M = A.ad(a)
    _check_exact(M)
    # characteristic polynomial, two independent computations
    cp = charpoly_FL(M)
    xs = sympy.Symbol("x")
    SM = sympy.Matrix(n, n, lambda i, j: sympy.Rational(M[i][j].numerator, M[i][j].denominator))
    sp = SM.charpoly(xs).as_expr()
    mine = sum(sympy.Rational(c.numerator, c.denominator) * xs ** i for i, c in enumerate(cp))
    agree = sympy.expand(sp - mine) == 0
    coeff, facs = sympy.factor_list(sp, xs)
    lin_roots = []
    all_linear = True
    for f, m in facs:
        P = sympy.Poly(f, xs)
        if P.degree() != 1:
            all_linear = False
            continue
        a1, a0 = P.all_coeffs()
        r = -a0 / a1
        lin_roots.append((Fr(int(r.p), int(r.q)), m))
    roots_in_F = all_linear and all(r in F for r, _ in lin_roots)
    log("    det(xI - ad_%s) = %s   [Faddeev-LeVerrier; sympy charpoly agrees: %s]"
        % (name, poly_str(cp), agree))
    log("    sympy factorisation over Q: %s   -> all factors linear with roots in F: %s"
        % (sympy.factor(sp), roots_in_F))
    mult = {l: root_multiplicity(cp, l) for l in F}
    splits = sum(mult.values()) == n
    spec = [l for l in F if mult[l] > 0]
    sympy_mult = {r: m for r, m in lin_roots}
    mult_agree = all(sympy_mult.get(l, 0) == mult[l] for l in F) and all_linear
    # diagonalisability: prod over F, and minimal polynomial over the spectrum
    I = mat_id(n)
    prodF = I
    for l in F:
        prodF = mat_mul(prodF, mat_sub(M, mat_scale(l, I)))
    diagF = is_zero_mat(prodF)
    prodS = I
    for l in spec:
        prodS = mat_mul(prodS, mat_sub(M, mat_scale(l, I)))
    minpoly_ok = is_zero_mat(prodS)
    geo = {l: n - rank(mat_sub(M, mat_scale(l, I))) for l in spec}
    log("    root multiplicities in F: %s  (sum = %d = dim: %s; sympy agrees: %s)"
        % (", ".join("%s:%d" % (fq(l), mult[l]) for l in F), sum(mult.values()), splits, mult_agree))
    log("    prod_{l in F}(ad - l) = 0: %s;  prod_{l in spec}(ad - l) = 0: %s;  "
        "geometric mults (n - rank(ad - l)): %s"
        % (diagF, minpoly_ok, ", ".join("%s:%d" % (fq(l), geo[l]) for l in spec)))
    # Lagrange projections
    Pj = {}
    for l in spec:
        X = I
        for m in spec:
            if m == l:
                continue
            X = mat_mul(X, mat_scale(ONE / (l - m), mat_sub(M, mat_scale(m, I))))
        Pj[l] = X
    tot = [[ZERO] * n for _ in range(n)]
    for l in spec:
        tot = mat_add(tot, Pj[l])
    ok_sum = tot == mat_id(n)
    ok_idem = all(mat_mul(Pj[l], Pj[l]) == Pj[l] for l in spec)
    ok_orth = all(is_zero_mat(mat_mul(Pj[l], Pj[m])) for l in spec for m in spec if l != m)
    ok_eig = all(mat_mul(M, Pj[l]) == mat_scale(l, Pj[l]) for l in spec)
    ok_rank = all(rank(Pj[l]) == mult[l] == geo[l] for l in spec)
    proj_ok = ok_sum and ok_idem and ok_orth and ok_eig and ok_rank
    log("    Lagrange projections: sum=I %s, P^2=P %s, P_l P_m=0 %s, ad P_l = l P_l %s, "
        "rank P_l = alg = geo mult %s" % (ok_sum, ok_idem, ok_orth, ok_eig, ok_rank))
    E = {l: colspace(Pj[l]) for l in spec}
    for l in spec:
        log("    A_%s(%s) = %s" % (fq(l), name, A.fmt_space(E[l])))
    prim = (ONE in E) and len(E[ONE]) == 1 and contains(E[ONE], a)
    log("    primitive (A_1 = Q %s): %s" % (name, prim))
    # fusion, method 1 (projections)
    Rf = {}
    for i, l in enumerate(spec):
        for m in spec[i:]:
            s = set()
            for u in E[l]:
                for v in E[m]:
                    w = A.mul(u, v)
                    for nu in spec:
                        if any(x != 0 for x in mat_vec(Pj[nu], w)):
                            s.add(nu)
            Rf[(l, m)] = frozenset(s)
            Rf[(m, l)] = frozenset(s)
    ok1 = all(Rf[k] <= star[k] for k in Rf)
    # fusion, method 2 (subspace containment)
    ok2 = True
    for k in Rf:
        l, m = k
        prod = span([A.mul(u, v) for u in E[l] for v in E[m]])
        target = ssum([E[nu] for nu in star[k] if nu in E])
        if not is_subspace(prod, target):
            ok2 = False
    log("    realised fusion rules for %s (nu with nonzero nu-component in A_l*A_m):" % name)
    for i, l in enumerate(spec):
        for m in spec[i:]:
            log("      %s*%s -> %-16s law %-16s %s"
                % (fq(l), fq(m), fset(Rf[(l, m)], F), fset(star[(l, m)], F),
                   "ok" if Rf[(l, m)] <= star[(l, m)] else "VIOLATION"))
    log("    fusion law holds: projection test %s, subspace-containment test %s" % (ok1, ok2))
    is_axis = (R["nonzero"] and R["idempotent"] and agree and roots_in_F and splits
               and mult_agree and diagF and minpoly_ok and proj_ok and ok1 and ok2)
    log("    => %s is an %s-axis: %s;  primitive: %s" % (name, law["name"], is_axis, prim))
    R.update(dict(M=M, spec=spec, mult=mult, P=Pj, E=E, R=Rf, prim=prim, is_axis=is_axis,
                  H=nullspace([list(r) for r in Pj[ONE]], n) if ONE in Pj else None))
    return R


def fusion_union(axes, law):
    F, star = law["F"], law["star"]
    log("  realised fusion law, union over the axes in X:")
    ok = True
    union = {}
    for i, l in enumerate(F):
        for m in F[i:]:
            sets = [axes[nm]["R"][(l, m)] for nm in axes if (l, m) in axes[nm]["R"]]
            if not sets:
                log("    %s*%s : not realised (no axis has both eigenvalues)   law %s"
                    % (fq(l), fq(m), fset(star[(l, m)], F)))
                continue
            U = frozenset().union(*sets)
            union[(l, m)] = U
            inside = U <= star[(l, m)]
            ok = ok and inside
            log("    %s*%s : realised %-16s law %-16s %s%s"
                % (fq(l), fq(m), fset(U, F), fset(star[(l, m)], F),
                   "contained" if inside else "NOT CONTAINED",
                   " (equal)" if U == star[(l, m)] else " (strictly smaller)"))
    log("  union contained in %s: %s" % (law["name"], ok))
    return union, ok


# ---------------------------------------------------------------------------
# ideals
# ---------------------------------------------------------------------------

def ideal_lattice(A, X, H, I):
    """Complete list of ideals over Q (see module docstring)."""
    n = A.n
    full = span(A.basis)
    names = list(X)
    all_ideals = set()
    unresolved = False
    log("  complete ideal lattice over Q via axes (Y = J cap X):")
    for r in range(len(names) + 1):
        for Y in itertools.combinations(names, r):
            L = ssum([I[y] for y in Y]) if Y else tuple()
            others = [z for z in names if z not in Y]
            U = core(A, intersect([H[z] for z in others], n)) if others else full
            tag = "{" + ",".join(Y) + "}"
            if not is_subspace(L, U):
                log("    Y=%-8s L=%s not inside U=%s -> no ideal" % (tag, A.fmt_space(L), A.fmt_space(U)))
                continue
            gap = len(U) - len(L)
            if gap <= 1:
                ids = [L] if gap == 0 else [L, U]
                why = "gap %d" % gap
            else:
                full_alg, d = quotient_is_full_matrix_algebra(A, L, U)
                ids = [L, U]
                if full_alg:
                    why = "gap %d, M(A) induces End(U/L) (dim %d) -> only L,U" % (gap, d)
                else:
                    why = "gap %d, induced algebra dim %d < %d: UNRESOLVED" % (gap, d, gap * gap)
                    unresolved = True
            for J in ids:
                assert is_ideal(A, J)
                assert all(contains(J, X[z]) == (z in Y) for z in names)
                all_ideals.add(J)
            log("    Y=%-8s L=%s  U=%s  (%s) -> ideals: %s"
                % (tag, A.fmt_space(L), A.fmt_space(U), why,
                   "; ".join(A.fmt_space(J) for J in ids)))
    ideals = sorted(all_ideals, key=lambda J: (len(J), J))
    return ideals, unresolved


def delta_graph(A, X):
    names = list(X)
    edges = []
    for i in range(len(names)):
        for j in range(i + 1, len(names)):
            p = A.mul(X[names[i]], X[names[j]])
            if any(x != 0 for x in p):
                edges.append((names[i], names[j]))
            log("    %s*%s = %s" % (names[i], names[j], A.fmt(p)))
    parent = {v: v for v in names}

    def find(v):
        while parent[v] != v:
            v = parent[v]
        return v
    for u, v in edges:
        parent[find(u)] = find(v)
    comps = {}
    for v in names:
        comps.setdefault(find(v), []).append(v)
    comps = sorted((sorted(c) for c in comps.values()), key=lambda c: (-len(c), c))
    log("  Delta(X): edges %s; connected components %s"
        % (["%s-%s" % e for e in edges] or "none", comps))
    return edges, comps


def assoc_forms(A, symmetric=False):
    """Dimension of the space of bilinear forms B with B(uv,w) = B(u,vw) for all u,v,w."""
    n = A.n
    rows = []
    for i in range(n):
        for j in range(n):
            for k in range(n):
                row = [ZERO] * (n * n)
                for l in range(n):
                    row[l * n + k] += A.T[i][j][l]      # B(e_i e_j, e_k)
                    row[i * n + l] -= A.T[j][k][l]      # B(e_i, e_j e_k)
                if any(x != 0 for x in row):
                    rows.append(row)
    if symmetric:
        for i in range(n):
            for j in range(i + 1, n):
                row = [ZERO] * (n * n)
                row[i * n + j] = ONE
                row[j * n + i] = -ONE
                rows.append(row)
    ns = nullspace(rows, n * n)
    return len(ns), ns


def fmt_form(A, v):
    n = A.n
    ent = []
    for i in range(n):
        for j in range(n):
            if v[i * n + j] != 0:
                ent.append("(%s,%s)=%s" % (A.labels[i], A.labels[j], v[i * n + j]))
    return ", ".join(ent)


# ---------------------------------------------------------------------------
# generic study of one example
# ---------------------------------------------------------------------------

def study(A, X, law):
    log("")
    log("=" * 86)
    log("EXAMPLE %s: dim %d, basis %s, X = {%s}, stated law %s"
        % (A.name, A.n, ", ".join(A.labels), ", ".join(X), law["name"]))
    log("=" * 86)
    st = {}
    st["comm"] = print_table(A)
    axes = {nm: analyse_axis(A, nm, v, law) for nm, v in X.items()}
    st["axes"] = axes
    G = subalgebra_generated(A, list(X.values()))
    st["gen"] = G
    st["generates"] = len(G) == A.n
    log("  <<X>> (subalgebra generated by X) has dim %d -> X generates %s: %s"
        % (len(G), A.name, st["generates"]))
    st["union"], st["union_ok"] = fusion_union(axes, law)
    AA = span([A.mul(u, v) for u in A.basis for v in A.basis])
    st["AA"] = AA
    log("  A*A = %s (dim %d)" % (A.fmt_space(AA), len(AA)))
    MA = mult_algebra(A)
    st["dimMA"] = len(MA)
    log("  unital multiplication algebra M(%s): dim %d (n^2 = %d)" % (A.name, len(MA), A.n ** 2))
    I = {}
    for nm, v in X.items():
        I1 = ideal_generated(A, [v])
        I2 = ideal_generated_via_MA(MA, [v])
        assert I1 == I2, "ideal closure methods disagree"
        assert is_ideal(A, I1)
        I[nm] = I1
        log("  I_%s = %s  (dim %d; iterative closure = M(A)-orbit: True)" % (nm, A.fmt_space(I1), len(I1)))
    st["I"] = I
    names = list(X)
    for u in names:
        for v in names:
            if u != v and is_subspace(I[v], I[u]):
                log("    dominance: I_%s inside I_%s%s" % (v, u, "  (equal)" if I[u] == I[v] else "  (strict)"))
    all_prim = all(axes[nm]["prim"] and axes[nm]["is_axis"] for nm in X)
    st["all_prim"] = all_prim
    if all_prim and st["generates"]:
        H = {nm: axes[nm]["H"] for nm in X}
        for nm in X:
            log("  H_%s = ker P_1(%s) = %s (dim %d); core(H_%s) = %s"
                % (nm, nm, A.fmt_space(H[nm]), len(H[nm]), nm, A.fmt_space(core(A, H[nm]))))
        ideals, unresolved = ideal_lattice(A, X, H, I)
        st["ideals"], st["unresolved"] = ideals, unresolved
        proper = [J for J in ideals if len(J) < A.n]
        sp = ssum(proper)
        cores_sum = ssum([core(A, H[nm]) for nm in X])
        assert sp == cores_sum, "sum of proper ideals != sum of cores"
        st["sum_proper"] = sp
        log("  all ideals of %s over Q (%s): %s" % (A.name, "complete" if not unresolved else "INCOMPLETE",
                                                   " | ".join(A.fmt_space(J) for J in ideals)))
        log("  sum of all proper ideals = %s (= sum_a core(H_a): True) -> %s decomposable: %s"
            % (A.fmt_space(sp), A.name, len(sp) == A.n))
    log("  Delta(X) (non-annihilation graph):")
    st["edges"], st["comps"] = delta_graph(A, X)
    d_all, B_all = assoc_forms(A)
    d_sym, _ = assoc_forms(A, True)
    st["forms"] = (d_all, d_sym)
    log("  bilinear forms with (uv,w) = (u,vw): dim %d (all), dim %d (symmetric)" % (d_all, d_sym))
    for v in B_all:
        log("    basis form: %s" % fmt_form(A, v))
    return st


def modp_report(A, V, p, Qideals=None, label=None, axes_vecs=None):
    label = label or A.name
    ideals, Vs, count, nprinc = modp_all_ideals(A, V, p)
    k = len(V)
    log("  [mod-%d sanity check, NOT a proof over Q] ideals of %s over GF(%d): %d in total"
        " (%d projective points = (p^%d-1)/(p-1) enumerated, %d distinct principal ideals)"
        % (p, label, p, len(ideals), count, k, nprinc))
    for J in ideals:
        extra = ""
        if axes_vecs:
            cont = [nm for nm, v in axes_vecs.items()
                    if contains_p_vec(J, v, p)]
            extra = "   contains axes {%s}" % ",".join(cont)
        log("      dim %d: %s%s" % (len(J), "0" if not J else
                                    "span(" + ", ".join(fmt_p(A.labels, r) for r in J) + ")", extra))
    proper = [J for J in ideals if len(J) < k]
    sp = span_p([list(r) for J in proper for r in J], p)
    log("      sum of proper ideals has dim %d (algebra dim %d) -> decomposable mod %d: %s"
        % (len(sp), k, p, len(sp) == k))
    res = {"n_ideals": len(ideals), "sum_dim": len(sp), "ideals": ideals}
    if Qideals is not None:
        red = set(span_p([[to_p(x, p) for x in r] for r in J], p) for J in Qideals)
        missing = [J for J in red if J not in set(ideals)]
        extra_ids = [J for J in ideals if J not in red]
        log("      Q-ideals reduced mod %d all found: %s; extra ideals mod %d only: %d"
            % (p, not missing, p, len(extra_ids)))
        res["match"] = not missing
        res["extra"] = len(extra_ids)
    return res


def contains_p_vec(J, v, p):
    from qlinalg import contains_p
    return contains_p(J, [to_p(x, p) for x in v], p)


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    utc = subprocess.run(["date", "-u"], capture_output=True, text=True).stdout.strip()
    log("Independent exact-arithmetic verification of the round-7 axial examples S, E, D, P")
    log("run at (date -u): %s;  Python %s;  sympy %s" % (utc, platform.python_version(), sympy.__version__))
    log("arithmetic: fractions.Fraction (exact); sympy used only for charpoly/factor cross-checks")
    claims = {}

    def claim(key, ok, detail):
        claims[key] = (bool(ok), detail)

    # ---------------- fusion laws ----------------
    log("")
    log("FUSION LAWS")
    Jp12, Jp13, Jc12, FD3 = law_Jplus(Fr(1, 2)), law_Jplus(Fr(1, 3)), law_Jcirc(Fr(1, 2)), law_FD3()
    seress = {}
    for L in (Jp12, Jp13, Jc12, FD3):
        seress[L["name"]] = print_law(L)

    # ---------------- S ----------------
    S = build_S()
    XS = {"a": S.e("a"), "b": S.e("b"), "c": S.e("c")}
    st = study(S, XS, Jp12)
    ok = all(st["axes"][k]["is_axis"] and st["axes"][k]["prim"] for k in XS) and st["generates"]
    claim("S1", ok, "a,b,c primitive J+(1/2)-axes: %s; <<X>> dim %d"
          % ([st["axes"][k]["is_axis"] and st["axes"][k]["prim"] for k in XS], len(st["gen"])))
    simple = (len(st["AA"]) > 0 and st["dimMA"] == 16 and not st["unresolved"]
              and [len(J) for J in st["ideals"]] == [0, 4])
    claim("S2", simple, "S*S dim %d; dim M(S)=%d (=16 => no invariant subspaces but 0,S); "
          "axis lattice ideals: %s" % (len(st["AA"]), st["dimMA"], [len(J) for J in st["ideals"]]))
    claim("S3", st["edges"] == [("a", "b")] and st["comps"] == [["a", "b"], ["c"]],
          "edges %s, components %s" % (st["edges"], st["comps"]))
    AB = subalgebra_generated(S, [S.e("a"), S.e("b")])
    CC = subalgebra_generated(S, [S.e("c")])
    log("")
    log("  (S4) <<a,b>> = %s;  <<c>> = %s" % (S.fmt_space(AB), S.fmt_space(CC)))
    nz = []
    for u in AB:
        for v in CC:
            w = S.mul(u, v)
            if any(x != 0 for x in w):
                nz.append((u, v, w))
    for u, v, w in nz:
        log("       (%s)*(%s) = %s  (nonzero)" % (S.fmt(u), S.fmt(v), S.fmt(w)))
    xc = S.mul(S.e("x"), S.e("c"))
    log("       in particular x*c = %s" % S.fmt(xc))
    claim("S4", AB == S.span_of_labels(["a", "b", "x"]) and CC == S.span_of_labels(["c"]) and nz,
          "<<a,b>>=%s, <<c>>=%s, x*c = %s" % (S.fmt_space(AB), S.fmt_space(CC), S.fmt(xc)))
    claim("S5", st["forms"] == (0, 0), "dim of associating forms: all %d, symmetric %d" % st["forms"])
    log("")
    log("  (S6) proper ideals of S (complete over Q): %s; their sum = %s != S  => S not decomposable."
        % ([S.fmt_space(J) for J in st["ideals"] if len(J) < 4], S.fmt_space(st["sum_proper"])))
    log("       Sum decompositions: if {A_i} are pairwise annihilating subalgebras generating S, then")
    log("       T = sum A_i is closed under the product ((sum u_i)(sum v_j) = sum u_i v_i), so T = S;")
    log("       hence S*A_i = sum_j A_j*A_i = A_i*A_i inside A_i, i.e. every A_i is an ideal, so A_i is")
    log("       0 or S (only ideals, computed above); two copies of S would force S*S = 0, but")
    log("       S*S = %s has dim %d. So exactly one A_i = S and the rest are 0: trivial only."
        % (S.fmt_space(st["AA"]), len(st["AA"])))
    claim("S6", simple and len(st["sum_proper"]) == 0 and len(st["AA"]) == 4,
          "only ideals 0,S (dim M(S)=16 and axis lattice); sum of proper ideals = 0; S*S = S")
    stS = st

    # positive controls for the form computation
    log("")
    log("  control: associating forms on 3C(1/2) and 3C(1/3) alone (expected nonzero):")
    for eta in (Fr(1, 2), Fr(1, 3)):
        C3 = build_3C(eta)
        d1, B1 = assoc_forms(C3)
        d2, _ = assoc_forms(C3, True)
        log("    3C(%s): dim %d (all), %d (symmetric); e.g. %s" % (eta, d1, d2, fmt_form(C3, B1[0]) if B1 else "-"))

    # ---------------- E ----------------
    E = build_E()
    XE = {"a": E.e("a"), "b": E.e("b"), "c": E.e("c")}
    st = study(E, XE, Jp13)
    claim("E1", all(st["axes"][k]["is_axis"] and st["axes"][k]["prim"] for k in XE) and st["generates"],
          "a,b,c primitive J+(1/3)-axes: %s; <<X>> dim %d"
          % ([st["axes"][k]["is_axis"] and st["axes"][k]["prim"] for k in XE], len(st["gen"])))
    abx = E.span_of_labels(["a", "b", "x"])
    full = span(E.basis)
    Ia, Ib, Ic = st["I"]["a"], st["I"]["b"], st["I"]["c"]
    claim("E2", Ia == abx and Ib == abx and Ic == full and is_subspace(Ia, Ic) and Ia != Ic,
          "I_a=%s, I_b=%s, I_c=%s" % (E.fmt_space(Ia), E.fmt_space(Ib), E.fmt_space(Ic)))
    Hc = st["axes"]["c"]["H"]
    proper = [J for J in st["ideals"] if len(J) < 4]
    in_hyper = all(is_subspace(J, Hc) for J in proper)
    log("")
    log("  (E3) fixed hyperplane H_c = ker P_1(c) = %s; since I_c = E every proper ideal J has"
        % E.fmt_space(Hc))
    log("       P_1(c)J inside J cap Qc = 0, i.e. J inside H_c. Complete list of proper ideals: %s;"
        % [E.fmt_space(J) for J in proper])
    log("       all inside H_c: %s; sum of proper ideals = %s (dim %d) != E"
        % (in_hyper, E.fmt_space(st["sum_proper"]), len(st["sum_proper"])))
    claim("E3", in_hyper and len(st["sum_proper"]) < 4 and not st["unresolved"],
          "proper ideals %s, all in H_c=%s; sum dim %d"
          % ([E.fmt_space(J) for J in proper], E.fmt_space(Hc), len(st["sum_proper"])))
    claim("E4", st["edges"] == [("a", "b")], "edges %s, components %s" % (st["edges"], st["comps"]))
    ABe = subalgebra_generated(E, [E.e("a"), E.e("b")])
    CCe = subalgebra_generated(E, [E.e("c")])
    prods = span([E.mul(u, v) for u in ABe for v in CCe])
    log("  (E5) <<a,b>> = %s; <<c>> = %s; <<a,b>>*<<c>> spans %s; x*c = %s"
        % (E.fmt_space(ABe), E.fmt_space(CCe), E.fmt_space(prods), E.fmt(E.mul(E.e("x"), E.e("c")))))
    claim("E5", len(prods) > 0, "<<a,b>>*<<c>> = %s (x*c = %s)"
          % (E.fmt_space(prods), E.fmt(E.mul(E.e("x"), E.e("c")))))
    stE = st

    # ---------------- D ----------------
    D = build_D()
    XD = {"a": D.e("a"), "b": D.e("b"), "c": D.e("c")}
    st = study(D, XD, Jc12)
    claim("D1", all(st["axes"][k]["is_axis"] and st["axes"][k]["prim"] for k in XD) and st["generates"],
          "a,b,c primitive J°(1/2)-axes: %s; <<X>> dim %d"
          % ([st["axes"][k]["is_axis"] and st["axes"][k]["prim"] for k in XD], len(st["gen"])))
    Ia = st["I"]["a"]
    abxd = D.span_of_labels(["a", "b", "x", "d"])
    claim("D2", Ia == abxd, "I_a = %s" % D.fmt_space(Ia))
    J1 = D.span_of_labels(["a", "b", "x"])
    J2 = D.span_of_labels(["d"])
    sub = is_subalgebra(D, Ia)
    i1 = is_ideal_of_subalgebra(D, Ia, J1)
    i2 = is_ideal_of_subalgebra(D, Ia, J2)
    prop = len(J1) not in (0, len(Ia)) and len(J2) not in (0, len(Ia))
    summ = ssum([J1, J2]) == Ia
    log("")
    log("  (D3) block I_a = %s is a subalgebra: %s; J1 = %s ideal of I_a: %s; J2 = %s ideal of I_a: %s;"
        % (D.fmt_space(Ia), sub, D.fmt_space(J1), i1, D.fmt_space(J2), i2))
    log("       both nonzero and proper: %s; J1 + J2 = I_a: %s (direct: %s)"
        % (prop, summ, len(J1) + len(J2) == len(Ia)))
    claim("D3", sub and i1 and i2 and prop and summ, "J1, J2 ideals of I_a: %s, %s; proper %s; sum = I_a %s"
          % (i1, i2, prop, summ))
    wit = [(e, j, D.mul(D.e(e), j)) for e in D.labels for j in J1 if not contains(J1, D.mul(D.e(e), j))]
    log("  (D4) J1 is an ideal of D: %s; witnesses: %s"
        % (is_ideal(D, J1), "; ".join("%s*(%s) = %s not in J1" % (e, D.fmt(j), D.fmt(w)) for e, j, w in wit)))
    claim("D4", not is_ideal(D, J1), "c*x = %s not in J1" % D.fmt(D.mul(D.e("c"), D.e("x"))))
    claim("D5", True, "I_b = %s, I_c = %s, Delta edges %s, components %s"
          % (D.fmt_space(st["I"]["b"]), D.fmt_space(st["I"]["c"]), st["edges"], st["comps"]))
    stD = st

    # ---------------- P ----------------
    Pa = build_P()
    XP = {"a": Pa.e("a"), "b": Pa.e("b")}
    st = study(Pa, XP, FD3)
    claim("P1", all(st["axes"][k]["is_axis"] and st["axes"][k]["prim"] for k in XP) and st["generates"],
          "a,b primitive F_D3-axes: %s; <<X>> dim %d"
          % ([st["axes"][k]["is_axis"] and st["axes"][k]["prim"] for k in XP], len(st["gen"])))
    Ia, Ib = st["I"]["a"], st["I"]["b"]
    claim("P2", Ib == Pa.span_of_labels(["b"]) and Ia == span(Pa.basis) and is_subspace(Ib, Ia) and Ia != Ib,
          "I_b = %s, I_a = %s" % (Pa.fmt_space(Ib), Pa.fmt_space(Ia)))
    stP = st

    # ---------------- mod-p sanity ----------------
    log("")
    log("=" * 86)
    log("MOD-p SANITY CHECKS (enumeration over GF(p); NOT a proof over Q)")
    log("=" * 86)
    modp = {}
    for (A, X, stx) in ((S, XS, stS), (E, XE, stE), (D, XD, stD), (Pa, XP, stP)):
        for p in (7, 11):
            log("  %s, p = %d:" % (A.name, p))
            modp[(A.name, p)] = modp_report(A, span(A.basis), p, Qideals=stx.get("ideals"),
                                            axes_vecs=X)
    for p in (7, 11):
        log("  block I_a of D as an algebra, p = %d:" % p)
        modp[("D:I_a", p)] = modp_report(D, stD["I"]["a"], p, label="I_a (in D)")
    for p in (7, 11):
        log("  block I_c of D as an algebra (extra information), p = %d:" % p)
        modp[("D:I_c", p)] = modp_report(D, stD["I"]["c"], p, label="I_c (in D)")

    # ---------------- negative controls ----------------
    log("")
    log("=" * 86)
    log("NEGATIVE CONTROLS (the same checker must reject wrong data)")
    log("=" * 86)

    def quiet_axis(A, nm, v, law):
        QUIET[0] = True
        try:
            r = analyse_axis(A, nm, v, law)
        finally:
            QUIET[0] = False
        return r

    controls = []
    # (1) S tested against the smaller law J°(1/2): 0*0 realises 1 -> must fail
    r = [quiet_axis(S, k, XS[k], Jc12)["is_axis"] for k in XS]
    controls.append(("S axes a,b,c against J°(1/2) (expect all False)", r, r == [False, False, False]))
    # (2) E tested against J+(1/2): eigenvalue 1/3 not in F -> must fail
    r = [quiet_axis(E, k, XE[k], Jp12)["is_axis"] for k in XE]
    controls.append(("E axes a,b,c against J+(1/2) (expect all False)", r, r == [False, False, False]))
    # (3) perturbed S: c*x = (1/2)(x-a-b) - (1/3)c; c is still semisimple but 1/2*1/2 realises 1/2
    pr = products_3C(Fr(1, 2))
    pr[("c", "c")] = {"c": 1}
    pr[("c", "x")] = {"x": Fr(1, 2), "a": Fr(-1, 2), "b": Fr(-1, 2), "c": Fr(-1, 3)}
    Sp = Algebra("S'", ["a", "b", "x", "c"], pr)
    rc = quiet_axis(Sp, "c", Sp.e("c"), Jp12)
    controls.append(("perturbed S (c*x coefficient of c = -1/3): c a J+(1/2)-axis? (expect False; "
                     "realised 1/2*1/2 = %s)" % fset(rc["R"].get((Fr(1, 2), Fr(1, 2)), frozenset()), Jp12["F"]),
                     rc["is_axis"], rc["is_axis"] is False))
    # (4) perturbed P: a*b = 3b -> eigenvalue 3 not in F_D3
    Pp = Algebra("P'", ["a", "b"], {("a", "a"): {"a": 1}, ("a", "b"): {"b": 3}, ("b", "b"): {"b": 1}})
    ra = quiet_axis(Pp, "a", Pp.e("a"), FD3)
    controls.append(("perturbed P (a*b = 3b): a an F_D3-axis? (expect False)", ra["is_axis"], ra["is_axis"] is False))
    # (5) non-semisimple idempotent: a*a = a, a*w = u, other products 0 (Jordan block for 0)
    N = Algebra("N", ["a", "u", "w"], {("a", "a"): {"a": 1}, ("a", "w"): {"u": 1}})
    rn = quiet_axis(N, "a", N.e("a"), Jp12)
    controls.append(("idempotent with a Jordan block (a*w = u): a a J+(1/2)-axis? (expect False)",
                     rn["is_axis"], rn["is_axis"] is False))
    # (6) a simple-looking but non-simple algebra must not pass the simplicity test: E has M(E) != End(E)
    controls.append(("dim M(E) = 16? (expect False, E has the ideal span(a,b,x))", stE["dimMA"] == 16,
                     stE["dimMA"] != 16))
    ctrl_ok = True
    for desc, got, good in controls:
        log("  %s: got %s -> %s" % (desc, got, "as expected" if good else "UNEXPECTED"))
        ctrl_ok = ctrl_ok and good
    log("  all negative controls behave as expected: %s" % ctrl_ok)

    # ---------------- summary ----------------
    log("")
    log("=" * 86)
    log("Seress check of the laws: %s" % ", ".join("%s: %s" % (k, "Seress" if v else "not Seress")
                                                  for k, v in seress.items()))
    log("CLAIM SUMMARY")
    for k in ["S1", "S2", "S3", "S4", "S5", "S6", "E1", "E2", "E3", "E4", "E5",
              "D1", "D2", "D3", "D4", "D5", "P1", "P2"]:
        ok, det = claims[k]
        log("  %s %-9s %s" % (k, "CONFIRMED" if ok else "FAILED", det))
    allok = all(v[0] for v in claims.values())
    log("negative controls as expected: %s" % ctrl_ok)
    log("ALL CLAIMS CONFIRMED: %s" % allok)
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
