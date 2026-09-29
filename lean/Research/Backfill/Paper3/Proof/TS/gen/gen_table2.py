#!/usr/bin/env python3
"""Generate the data modules of Table 2 (paper 3, version 2).

For d = 3, 4, 5 (n = 2d): the d-regular graphs on n vertices up to isomorphism, found by closing
{K_{d,d}} under 2-switches (canonical form: u1 is the smallest of the four vertices, same order as
`P3TS.tuples`); for every valid 2-switch of every representative a certificate (j, sigma,
sigma^-1) with sigma an isomorphism from the switched graph onto representative j (sigma packed
four bits per vertex); histograms of e(A) over all vertex sets (padded to n(n-1)/2 + 1 entries);
N_{<=t} profiles for t <= d^2; for d = 5 the pairs of classes with equal profiles and an invariant
(`cnDist` or `triDist`) separating each of them. Nothing here is trusted: the kernel checks every
fact (P3.TS.Code, P3.TS.Count). Usage: python3 gen_table2.py  (writes ../D3.lean, ../D4.lean,
../D5Data.lean, ../D5C0.lean .. ../D5C5.lean, ../D5.lean).
In the release tree the development module names `P3.X` are renamed `Research.Backfill.Paper3.Proof.X`
(import lines and comments); apart from that, the output equals the data modules byte for byte.
"""
import collections
from pathlib import Path
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher

OUT = Path(__file__).resolve().parent.parent


def adj_of(E, n):
    A = [[False] * n for _ in range(n)]
    for a, b in E:
        A[a][b] = A[b][a] = True
    return A


def tonx(E, n):
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from(E)
    return G


def inv(E, n):  # bucketing invariant (only used to speed up the search)
    A = adj_of(E, n)
    N = [set(j for j in range(n) if A[i][j]) for i in range(n)]
    vi = []
    for v in range(n):
        t = sum(1 for a in N[v] for b in N[v] if a < b and A[a][b])
        c1 = tuple(sorted(len(N[u] & N[v]) for u in N[v]))
        c2 = tuple(sorted(len(N[u] & N[v]) for u in range(n) if u != v and u not in N[v]))
        vi.append((t, c1, c2))
    return tuple(sorted(vi))


def switched(E, t):
    u1, w1, u2, w2 = t
    F = set(E)
    F.discard((min(u1, w1), max(u1, w1)))
    F.discard((min(u2, w2), max(u2, w2)))
    F.add((min(u1, w2), max(u1, w2)))
    F.add((min(u2, w1), max(u2, w1)))
    return frozenset(F)


def canon_tuples(n):  # the order of `P3TS.tuples n`
    for u1 in range(n):
        for w1 in range(u1 + 1, n):
            for u2 in range(u1 + 1, n):
                for w2 in range(u1 + 1, n):
                    yield (u1, w1, u2, w2)


def valid(A, t):  # `P3TS.validB`
    u1, w1, u2, w2 = t
    return A[u1][w1] and A[u2][w2] and not A[u1][w2] and not A[u2][w1] and u2 != w1 and u1 != w2


def classes(d):
    n = 2 * d
    start = frozenset((a, b) for a in range(d) for b in range(d, 2 * d))
    reps, nxreps = [start], [tonx(start, n)]
    buckets = collections.defaultdict(list)
    buckets[inv(start, n)].append(0)
    certs, i = [], 0
    while i < len(reps):
        A = adj_of(reps[i], n)
        cl = []
        for t in canon_tuples(n):
            if not valid(A, t):
                continue
            E2 = switched(reps[i], t)
            G2 = tonx(E2, n)
            key = inv(E2, n)
            found = None
            for j in buckets[key]:
                gm = GraphMatcher(G2, nxreps[j])
                if gm.is_isomorphic():
                    found = (j, [gm.mapping[a] for a in range(n)])
                    break
            if found is None:
                reps.append(E2)
                nxreps.append(G2)
                buckets[key].append(len(reps) - 1)
                found = (len(reps) - 1, list(range(n)))
            j, s = found
            # check the certificate: s maps the switched graph onto rep j
            Aj = adj_of(reps[j], n)
            A2 = adj_of(E2, n)
            assert sorted(s) == list(range(n))
            assert all(A2[a][b] == Aj[s[a]][s[b]] for a in range(n) for b in range(n))
            cl.append((t, j, s))
        certs.append(cl)
        i += 1
    return reps, certs


def code(E, n):
    return sum((1 << (a * n + b)) + (1 << (b * n + a)) for a, b in E)


def hist(E, n):
    L = n * (n - 1) // 2 + 1
    h = [0] * L
    for m in range(1 << n):
        h[sum(1 for a, b in E if (m >> a & 1) and (m >> b & 1))] += 1
    return h


def pack(s):
    return sum(v << (4 * i) for i, v in enumerate(s))


def inverse(s):
    r = [0] * len(s)
    for i, v in enumerate(s):
        r[v] = i
    return r


def cn_dist(E, n):
    A = adj_of(E, n)
    c = collections.Counter()
    for u in range(n):
        for v in range(n):
            if u != v:
                c[(A[u][v], sum(1 for w in range(n) if A[u][w] and A[v][w]))] += 1
    return c


def tri_dist(E, n):
    A = adj_of(E, n)
    c = collections.Counter()
    for v in range(n):
        c[sum(1 for a in range(n) for b in range(n) if A[v][a] and A[v][b] and A[a][b])] += 1
    return c


def lst(v):
    return "[" + ", ".join(str(x) for x in v) + "]"


def wrap(items, indent="    ", width=100, first=2):
    """A Lean list literal of the given item strings, wrapped at `width` columns (the first line
    is preceded by `first` characters)."""
    lines, cur = [], " " * first + "["
    for k, it in enumerate(items):
        piece = it + ("," if k + 1 < len(items) else "]")
        start = cur.endswith("[") or cur == indent
        if len(cur) + 1 + len(piece) > width and not start:
            lines.append(cur)
            cur = indent + piece
        else:
            cur = cur + ("" if start else " ") + piece
    if not items:
        cur = " " * first + "[]"
    lines.append(cur)
    return "\n".join(lines)[first:]


def certs_lean(cl):
    return wrap([f"({j}, {pack(s)}, {pack(inverse(s))})" for _, j, s in cl])


CLAIMS = {3: (2, "[(1, 28, 24)]", "[0, 2]"),
          4: (6, "[(1, 61, 47), (3, 137, 127), (5, 187, 171)]", "[0, 4, 6]"),
          5: (60, "[(1, 116, 88), (2, 203, 188), (3, 321, 288), (5, 524, 448), (7, 679, 648), "
                  "(8, 783, 748),\n      (11, 908, 868)]", "[0, 4, 6, 9, 10, 12]")}


def data_block(d, reps, n, k):
    hs = [hist(E, n) for E in reps]
    prof = [[sum(h[:t + 1]) for t in range(d * d + 1)] for h in hs]
    L = []
    for i, E in enumerate(reps):
        L.append(f"def c{i} : ℕ := {code(E, n)}\n")
    L.append(f"/-- Adjacency codes of the {k} representatives. -/\n"
             f"def codes : List ℕ :=\n  {wrap([f'c{i}' for i in range(k)])}\n")
    for i, h in enumerate(hs):
        L.append(f"def h{i} : List ℕ :=\n  {wrap([str(x) for x in h])}\n")
    L.append(f"/-- Histograms of `e(A)`: entry `s` is the number of vertex sets with `s` edges. -/\n"
             f"def hists : List (List ℕ) :=\n  {wrap([f'h{i}' for i in range(k)])}\n")
    for i, p in enumerate(prof):
        L.append(f"def p{i} : List ℕ :=\n  {wrap([str(x) for x in p])}\n")
    L.append("/-- `N_{≤t}` for `t = 0, …, d²`. -/\n"
             f"def prof : List (List ℕ) :=\n  {wrap([f'p{i}' for i in range(k)])}\n")
    return "\n".join(L), prof


def common_defs(d, k):
    n = 2 * d
    Ln = n * (n - 1) // 2 + 1
    return f"""
/-- The representatives. -/
abbrev R (i : Fin {k}) : SimpleGraph (Fin (2 * {d})) := ofCode (2 * {d}) (codes.getD i 0)

/-- `N_{{≤t}}` of the representatives (from the table `prof`). -/
def P (i : Fin {k}) (t : ℕ) : ℕ := (prof.getD i []).getD t 0

theorem wf_deg : allLt {k} (fun j => wfB (2 * {d}) (codes.getD j 0) &&
    allLt (2 * {d}) (fun v => degB (2 * {d}) (codes.getD j 0) v == {d})) = true := by
  decide +kernel

theorem hist_ok : allLt {k} (fun j => (hists.getD j []).length == {Ln} &&
    (hists.getD j []).all (fun x => decide (x < 2048))) = true := by
  decide +kernel

theorem prof_ok : allLt {k} (fun j => (prof.getD j []).length == {d} ^ 2 + 1 && allLt ({d} ^ 2 + 1)
    (fun t => (prof.getD j []).getD t 0 == sumLt (t + 1) (fun s => (hists.getD j []).getD s 0))) =
    true := by
  decide +kernel

theorem wf (j : ℕ) (hj : j < {k}) : wfB (2 * {d}) (codes.getD j 0) = true := by
  have h := allLt_iff.1 wf_deg j hj
  rw [Bool.and_eq_true] at h
  exact h.1

theorem hdeg (i : Fin {k}) (v : Fin (2 * {d})) : (nbr (R i) v).card = {d} := by
  rw [card_nbr_ofCode (wf i i.isLt)]
  have h := allLt_iff.1 wf_deg i i.isLt
  rw [Bool.and_eq_true, allLt_iff] at h
  simpa using h.2 v v.isLt

theorem prof_len (i : Fin {k}) : (prof.getD i []).length = {d} ^ 2 + 1 := by
  have h := allLt_iff.1 prof_ok i i.isLt
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem hK : Nonempty (Kdd {d} ≃g R 0) :=
  ⟨⟨finSumFinEquiv.trans (finCongr (by norm_num)), by intro a b; revert a b; decide⟩⟩
"""


def hP_block(d, k):
    n = 2 * d
    return f"""
theorem hP (i : Fin {k}) (t : ℕ) (ht : t ≤ {d} ^ 2) (_ : DecidableRel (R i).Adj) :
    iCount (R i) t = P i t := by
  have hh := allLt_iff.1 hist_ok i i.isLt
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hh
  rw [iCount_ofCode_eq (wf i i.isLt) (by norm_num) (hh.1.trans (by norm_num)) hh.2
    (poly_all i i.isLt) t]
  have hp := allLt_iff.1 prof_ok i i.isLt
  rw [Bool.and_eq_true, allLt_iff] at hp
  have hp' := hp.2 t (Nat.lt_succ_of_le ht)
  rw [beq_iff_eq, sumLt_eq] at hp'
  exact hp'.symm

theorem hclosed : ∀ i (u₁ w₁ u₂ w₂ : Fin (2 * {d})), u₁ < w₁ → u₁ < u₂ → u₁ < w₂ →
    IsSwitch (R i) u₁ w₁ u₂ w₂ → ∃ j, Nonempty (twoSwitch (R i) u₁ w₁ u₂ w₂ ≃g R j) :=
  fun i u₁ w₁ u₂ w₂ h1 h2 h3 hs =>
    closure_of_chk (fun j hj => wf j hj) i.isLt (chk_all i i.isLt) u₁ w₁ u₂ w₂ h1 h2 h3 hs
"""


def combine_block(d, k):
    n = 2 * d
    ch = ", ".join(f"chk{i}" for i in range(k))
    po = ", ".join(f"poly{i}" for i in range(k))
    return f"""
/-- The certificates of all classes. -/
def certs : List (List (ℕ × ℕ × ℕ)) :=
  {wrap([f'certs{i}' for i in range(k)])}

theorem chk_all : ∀ i < {k},
    chk (2 * {d}) {k} (codes.getD i 0) codes (tuples (2 * {d})) (certs.getD i []) = true := by
  intro i hi
  interval_cases i
  exacts {wrap([f'chk{i}' for i in range(k)], first=9)}

theorem poly_all : ∀ i < {k}, polyH (2 * {d}) (codes.getD i 0) = ofD (hists.getD i []) := by
  intro i hi
  interval_cases i
  exacts {wrap([f'poly{i}' for i in range(k)], first=9)}
"""


def class_block(d, k, i, cl):
    n = 2 * d
    return (f"def certs{i} : List (ℕ × ℕ × ℕ) :=\n  {certs_lean(cl)}\n\n"
            f"theorem chk{i} : chk (2 * {d}) {k} (codes.getD {i} 0) codes (tuples (2 * {d})) certs{i} = true := by\n"
            f"  decide +kernel\n\n"
            f"theorem poly{i} : polyH (2 * {d}) (codes.getD {i} 0) = ofD (hists.getD {i} []) := by\n"
            f"  decide +kernel\n")


def row_block(d, k, specials):
    fails, uniq = CLAIMS[d][1], CLAIMS[d][2]
    if specials:
        special = "(fun i j => (i.val, j.val) ∈ specialPairs)"
        special_prop = "(i.val, j.val) ∈ specialPairs"
        hspec = "hspec"
    else:
        special = "(fun _ _ => False)"
        special_prop = "False"
        hspec = "(fun _ _ h => h.elim)"
    return f"""
theorem sep : ∀ i j : Fin {k}, i ≠ j →
    prof.getD i [] ≠ prof.getD j [] ∨ {special_prop} := by
  decide +kernel

theorem hsep : ∀ i j : Fin {k}, i ≠ j →
    (∃ t ≤ {d} ^ 2, P i t ≠ P j t) ∨ {special} i j := by
  intro i j hij
  rcases sep i j hij with h | h
  · obtain ⟨t, ht, hne⟩ := exists_getD_ne h (prof_len i) (prof_len j)
    exact Or.inl ⟨t, Nat.lt_succ_iff.1 ht, hne⟩
  · exact Or.inr h

/-- **Table 2, row `d = {d}`.** -/
theorem row : Table2Row {d} {k}
    {fails}
    {uniq} :=
  table2Row_of_data R 0 P hdeg
    (noniso_of_prof R P hP {special} {hspec} hsep) hclosed hP hK
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
"""


HEAD = """set_option autoImplicit false
"""


def special_block(d, reps, n, specials_unordered):
    """IsEmpty proofs for the pairs with equal profiles, by `cnDist` or `triDist`."""
    L = []
    pairs = []
    for i, j in specials_unordered:
        ci, cj = cn_dist(reps[i], n), cn_dist(reps[j], n)
        w = None
        for key in sorted(set(ci) | set(cj)):
            if ci[key] != cj[key]:
                w = ("cn", key)
                break
        if w is None:
            ti, tj = tri_dist(reps[i], n), tri_dist(reps[j], n)
            for key in sorted(set(ti) | set(tj)):
                if ti[key] != tj[key]:
                    w = ("tri", key)
                    break
        assert w is not None
        if w[0] == "cn":
            a, c = w[1]
            inv_line = f"cnDist_iso φ {'true' if a else 'false'} {c}"
        else:
            inv_line = f"triDist_iso φ {w[1]}"
        L.append(f"""theorem ne_{i}_{j} : IsEmpty (R {i} ≃g R {j}) :=
  ⟨fun φ => by
    have h := {inv_line}
    revert h
    decide⟩
""")
        pairs.append((i, j))
    # hspec
    cases = []
    for i, j in pairs:
        cases.append(f"  · exact ne_{i}_{j}")
        cases.append(f"  · exact ⟨fun φ => (ne_{i}_{j}).false φ.symm⟩")
    toks = ["⟨rfl, rfl⟩"] * (2 * len(pairs))
    plines, cur = [], "  rcases h with ("
    for t_i, tok in enumerate(toks):
        piece = tok + (" |" if t_i + 1 < len(toks) else ")")
        if len(cur) + 1 + len(piece) > 100 and not cur.endswith("("):
            plines.append(cur)
            cur = "    " + piece
        else:
            cur = cur + ("" if cur.endswith("(") else " ") + piece
    plines.append(cur)
    pat = "\n".join(plines)[len("  rcases h with "):]
    L.append(f"""theorem hspec : ∀ i j : Fin 60, (i.val, j.val) ∈ specialPairs → IsEmpty (R i ≃g R j) := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ h
  simp only [specialPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with {pat}
""" + "\n".join(cases) + "\n")
    return "\n".join(L)


def main():
    for d in [3, 4, 5]:
        n = 2 * d
        reps, certs = classes(d)
        k = len(reps)
        assert k == CLAIMS[d][0], (d, k)
        data, prof = data_block(d, reps, n, k)
        specials = []
        if d == 5:
            grp = collections.defaultdict(list)
            for i, p in enumerate(prof):
                grp[tuple(p)].append(i)
            su = [tuple(g) for g in grp.values() if len(g) > 1]
            assert all(len(g) == 2 for g in su)
            specials = []
            for i, j in su:
                specials += [(i, j), (j, i)]
        ns = f"P3TS.D{d}"
        if d in (3, 4):
            body = [f"""import P3.TS.Count
import P3.TS.Row

/-!
# Table 2, `d = {d}`: data and kernel checks

The {k} classes of {d}-regular graphs on {n} vertices (adjacency codes), the histograms and
`N_{{≤t}}` profiles, and the 2-switch certificates; generated by `gen/gen_table2.py`, every fact
checked by the kernel (`decide +kernel` on the checkers of `P3.TS.Code` and `P3.TS.Count`).
-/

""" + HEAD + f"""
namespace {ns}

open Finset BackfillPaper3.Challenge P3TS

""", data, common_defs(d, k)]
            for i in range(k):
                body.append(class_block(d, k, i, certs[i]))
            body.append(combine_block(d, k))
            body.append(hP_block(d, k))
            body.append(row_block(d, k, []))
            body.append(f"\nend {ns}\n")
            (OUT / f"D{d}.lean").write_text("\n".join(body))
        else:
            head = f"""import P3.TS.Count
import P3.TS.Row
import P3.TS.Invariants

/-!
# Table 2, `d = 5`: data

The 60 classes of 5-regular graphs on 10 vertices (adjacency codes), histograms of `e(A)`,
`N_{{≤t}}` profiles; kernel checks of symmetry, degrees and the profile table; the pairs of classes
with equal profiles are separated by `cnDist` / `triDist`. Generated by `gen/gen_table2.py`.
-/

""" + HEAD + f"""
namespace {ns}

open Finset BackfillPaper3.Challenge P3TS

"""
            sp = wrap([f"({i}, {j})" for i, j in specials])
            spec_def = f"""
/-- Pairs of classes with the same `N_{{≤t}}` profile. -/
def specialPairs : List (ℕ × ℕ) :=
  {sp}

"""
            su = [(i, j) for (i, j) in specials if i < j]
            (OUT / "D5Data.lean").write_text(head + data + common_defs(d, k) + spec_def +
                                             special_block(d, reps, n, su) + f"\nend {ns}\n")
            for b in range(6):
                lo, hi = 10 * b, 10 * b + 10
                body = [f"""import P3.TS.D5Data

/-!
# Table 2, `d = 5`: 2-switch certificates and histograms of classes {lo}–{hi - 1}

Generated by `gen/gen_table2.py`; checked by the kernel.
-/

""" + HEAD + f"""
namespace {ns}

open Finset BackfillPaper3.Challenge P3TS

"""]
                for i in range(lo, hi):
                    body.append(class_block(d, k, i, certs[i]))
                body.append(f"\nend {ns}\n")
                (OUT / f"D5C{b}.lean").write_text("\n".join(body))
            row = row_block(d, k, specials)
            (OUT / "D5.lean").write_text(f"""import P3.TS.D5C0
import P3.TS.D5C1
import P3.TS.D5C2
import P3.TS.D5C3
import P3.TS.D5C4
import P3.TS.D5C5

/-!
# Table 2, `d = 5`

Assembles the kernel checks of `P3.TS.D5Data` and `P3.TS.D5C0`–`P3.TS.D5C5` into
`Table2Row 5 60 …` with `table2Row_of_data`. Generated by `gen/gen_table2.py`.
-/

""" + HEAD + f"""
namespace {ns}

open Finset BackfillPaper3.Challenge P3TS
""" + combine_block(d, k) + hP_block(d, k) + row + f"\nend {ns}\n")
        print("d", d, "classes", k, "certificates", sum(len(c) for c in certs),
              "special pairs", len(specials) // 2)


if __name__ == "__main__":
    main()
