import Mathlib

set_option autoImplicit false

/-!
# Paper 4 back-fill: challenge statements (version 2)

Paper: H. Dong, *Answers to three problems of Hak, Kozerenko and Oliynyk on the triameter of
graphs* (`outputs/release/ai4math-results/papers/hko-triameter/note.tex`, release v1.4.0 and later,
11 pages).

This file contains **definitions and statements only**: every statement is a `def … : Prop`.
It imports only Mathlib. Nothing here is proved. After independent review it is frozen by
SHA-256; the proofs go into separate modules, and `Check.lean` will contain
`theorem check_X : Challenge.X := …` for every `X` below (tiers 1 and 2).

Version 2 = version 1 (SHA-256 `06725c85…8321`, reviewed in
`work/lean-backfill/paper4/REVIEW-CHALLENGE.md`) plus the review's fix of `Sec5_FP_symm`, the
tier-2 count `Sec4_count_candidates`, and without the tier-3 statements (every change is listed
in `work/lean-backfill/paper4/DIFF-v2.md`).

## Numbering

The paper has three unnumbered theorems (Theorems A, B, C) and a shared counter for
Lemma 1 (`lem:grid`), Lemma 2 (`lem:core`), Proposition 3 (`prop:ineq`), Remark 4
(`rem:sharp`) and Remark 5 (`rem:h11`). The remarks contain mathematical claims, so they get
`def`s too, as do the load-bearing unnumbered claims of Sections 2–5 and 8 (`Sec2_…`, `Sec3_…`,
…). Names ending in `_i`, `_ii`, … split one theorem into its separate assertions.

## Tiers

* **Tier 1** — every theorem, lemma, proposition, remark and in-text mathematical claim that the
  paper asserts, except the pure counts of the enumeration programs. All must be proved.
* **Tier 2** — counts reported for the enumeration of Section 4 (`Sec4_count_median`,
  `Sec4_count_triangleFree7`, `Sec4_count_candidates`, `Sec4_count_labelled`, `Sec4_aut`).
  They are numbers printed in the paper and have a kernel-checkable route; by the user's decision
  of 2026-09-27 they are kept in the paper and must be proved.
* **Dropped (formerly tier 3)** — by the same decision, claims that cannot be fully formalized are
  deleted from the corrected paper, so they are not stated here: the uniqueness of `H₁₁` (Remark 5,
  last sentence), the §6 counts (numbers of distance-hereditary graphs, 49,394, 48,108, 5,888,
  1,692, 29,263, and the random tests), and the §4 counts of connected labelled graphs (OEIS
  A001187).

## Conventions (the full table is `work/lean-backfill/paper4/STATEMENTS.md`)

* A graph is a Mathlib `SimpleGraph` on a vertex type `V : Type` with `[Fintype V]` ("finite and
  simple", paper §1). "A graph with `n` vertices" means `Fintype.card V = n`. Isomorphism is
  Mathlib's `G ≃g H`.
* Distances are Mathlib's `SimpleGraph.dist` (a natural number; `0` between vertices in different
  components, which never matters here because every statement assumes connectedness); the
  diameter is `SimpleGraph.diam`, the eccentricity `SimpleGraph.eccent`, the extended diameter
  `SimpleGraph.ediam`.
* `triDist`, `triameter`, `IsTriametral`, `IsDiametral`, `IsPeripheral`, `IsPeripheralPair`,
  `InInterval`, `IsMedian`, `Question3`, `Question3'`, `Question3'Pair`, `Question4`,
  `Question4'`, `Problem1Claim`, `Problem1ClaimPair`, `Problem2Claim`, `Problem2ClaimWeak`,
  `g1Edges`, `G1`, `g2Edges`, `G2`, `FP`, `FourPointBM`, `Problem3ClaimFP`, `f1gEdges`, `F1G`,
  `f1hEdges`, `F1H` are verbatim copies of the definitions in the released modules
  `Research.HKOTriameter` and `Research.HKOTriameterDH` (v1.4.0), so that the already-proved
  results can be linked by definitional unfolding.
* The triameter is the maximum over **ordered triples with repetitions allowed** (paper §2, "the
  vertices in the definition of `tr(G)` need not be distinct"). Questions (Q3), (Q3′), (Q4),
  (Q4′) are stated for every triple / pair / vertex with repetitions allowed, and (Q4), (Q4′) with
  the **weak reading** (the added vertices are unrestricted), which is how the paper defines them
  (§1). The strong readings (`Question4Strong`, `Question4'Strong`) and the distinct-vertex
  versions of (Q3), (Q3′) are separate definitions; §2 of the paper relates them
  (`Sec2_readings_…`).
* "Peripheral" is `eccent = ediam` (`IsPeripheral`); the paper's literal wording "belongs to a
  diametral pair" is `IsPeripheralPair`; `Sec2_peripheral_iff` states that they agree.
* A **distance-hereditary** graph is a connected graph every connected induced subgraph of which
  is isometric (paper §2, after Howorka): `IsDistanceHereditary`. Induced subgraphs are Mathlib's
  `G.induce s` on the subtype `↥s`.
* The graphs `G1`, `G2` have vertex set `Fin 8` and the paper's labels; `H11` has vertex set
  `Fin 11`; HKO's Figure 2 graph (`HKOFig2`) has vertex set `Fin 12`, with the labels of
  `work/round6/hko-triameter/code/hko_fig0_check.py` (`x = 0`, `b = 2`, `y = 5`, `a = 7`,
  `c = 10`); the MathOverflow graph (`MOGraph`) has vertex set `Fin 11` with
  `s,u₁,u₂,a,v₁,v₂,b,x,w₁,w₂,c = 0,…,10`. HKO's Figure 3 graphs `G`, `H` are `F1G` (`y,m,a,b,c,x
  = 0,…,5`) and `F1H` (`a,b,c,x,m,y = 0,…,5`), as in the released module.
* `ℤ^k` is `Fin k → ℤ`; `Γ(S)` is `gridGraph S` on the subtype of the finset `S`.
-/

namespace BackfillPaper4.Challenge

open SimpleGraph Finset

/-! ## 1. Metric notions, questions and problems (verbatim from `Research.HKOTriameter`) -/

section Defs

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- `d_G(u,v,w) = d_G(u,v) + d_G(u,w) + d_G(v,w)`. -/
noncomputable def triDist (u v w : V) : ℕ :=
  G.dist u v + G.dist u w + G.dist v w

/-- `tr(G)`: the maximum of `triDist` over all ordered triples (repetitions allowed). -/
noncomputable def triameter : ℕ :=
  (univ : Finset (V × V × V)).sup fun t => triDist G t.1 t.2.1 t.2.2

/-- A triple is triametral if `d_G(u,v,w) = tr(G)`. -/
def IsTriametral (u v w : V) : Prop :=
  triDist G u v w = triameter G

/-- A pair is diametral if `d_G(u,v) = diam(G)`. -/
def IsDiametral (u v : V) : Prop :=
  G.dist u v = G.diam

/-- A vertex is peripheral if its eccentricity equals the diameter. -/
def IsPeripheral (u : V) : Prop :=
  G.eccent u = G.ediam

/-- The paper's literal wording: a vertex is peripheral if it belongs to some diametral pair. -/
def IsPeripheralPair (u : V) : Prop :=
  ∃ v, IsDiametral G u v

/-- `x ∈ [u,v]`, i.e. `d(u,x) + d(x,v) = d(u,v)`. -/
def InInterval (u v x : V) : Prop :=
  G.dist u x + G.dist x v = G.dist u v

/-- Median graph: connected, and `|[u,v] ∩ [u,w] ∩ [v,w]| = 1` for all `u, v, w`. -/
def IsMedian : Prop :=
  G.Connected ∧
    ∀ u v w : V, ∃! x, InInterval G u v x ∧ InInterval G u w x ∧ InInterval G v w x

/-- (Q3′): every triametral triple contains a peripheral vertex. -/
def Question3' : Prop :=
  ∀ a b c : V, IsTriametral G a b c → IsPeripheral G a ∨ IsPeripheral G b ∨ IsPeripheral G c

/-- (Q3′) with the pair-based definition of "peripheral". -/
def Question3'Pair : Prop :=
  ∀ a b c : V, IsTriametral G a b c →
    IsPeripheralPair G a ∨ IsPeripheralPair G b ∨ IsPeripheralPair G c

/-- (Q3): every triametral triple contains a diametral pair. -/
def Question3 : Prop :=
  ∀ a b c : V, IsTriametral G a b c → IsDiametral G a b ∨ IsDiametral G a c ∨ IsDiametral G b c

/-- (Q4), weak reading: every diametral pair extends to a triametral triple (`z` unrestricted). -/
def Question4 : Prop :=
  ∀ x y : V, IsDiametral G x y → ∃ z, IsTriametral G x y z

/-- (Q4′), weak reading: every peripheral vertex belongs to a triametral triple. -/
def Question4' : Prop :=
  ∀ x : V, IsPeripheral G x → ∃ y z, IsTriametral G x y z

end Defs

/-- Problem 1 as a claim: every (finite) median graph has (Q3′). -/
def Problem1Claim : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsMedian G → Question3' G

/-- Problem 1 with the pair-based definition of "peripheral". -/
def Problem1ClaimPair : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsMedian G → Question3'Pair G

/-- Problem 2 as a claim: every (finite) median graph has (Q4). -/
def Problem2Claim : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsMedian G → Question4 G

/-- The weaker form of Problem 2: every (finite) median graph has (Q4′). -/
def Problem2ClaimWeak : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsMedian G → Question4' G

/-! ## 2. Further definitions (new in the back-fill) -/

section MoreDefs

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- (Q4), strong reading: the third vertex must differ from `x` and `y`. -/
def Question4Strong : Prop :=
  ∀ x y : V, IsDiametral G x y → ∃ z, z ≠ x ∧ z ≠ y ∧ IsTriametral G x y z

/-- (Q4′), strong reading: a triametral triple of three distinct vertices through `x`. -/
def Question4'Strong : Prop :=
  ∀ x : V, IsPeripheral G x → ∃ y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ IsTriametral G x y z

/-- (Q3) restricted to triples of distinct vertices. -/
def Question3Distinct : Prop :=
  ∀ a b c : V, a ≠ b → a ≠ c → b ≠ c → IsTriametral G a b c →
    IsDiametral G a b ∨ IsDiametral G a c ∨ IsDiametral G b c

/-- (Q3′) restricted to triples of distinct vertices. -/
def Question3'Distinct : Prop :=
  ∀ a b c : V, a ≠ b → a ≠ c → b ≠ c → IsTriametral G a b c →
    IsPeripheral G a ∨ IsPeripheral G b ∨ IsPeripheral G c

end MoreDefs

/-- Distance-hereditary graph (paper §2, after Howorka): `G` is connected and every connected
induced subgraph `H = G[s]` is isometric, `d_H(u,v) = d_G(u,v)` for all `u, v ∈ s`. -/
def IsDistanceHereditary {V : Type*} (G : SimpleGraph V) : Prop :=
  G.Connected ∧
    ∀ s : Set V, (G.induce s).Connected → ∀ u v : s, (G.induce s).dist u v = G.dist u v

/-- `v` is a pendant vertex: its neighbourhood (Mathlib's `neighborSet`) is a single vertex. -/
def IsPendant {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ∃ u, G.neighborSet v = {u}

/-- `v` and `t` are twins: distinct, with `N(v) ∖ {t} = N(t) ∖ {v}` (adjacent to each other or not:
true or false twins). -/
def AreTwins {V : Type*} (G : SimpleGraph V) (v t : V) : Prop :=
  v ≠ t ∧ G.neighborSet v \ {t} = G.neighborSet t \ {v}

/-! ## 3. The four-point condition (verbatim `FP`, `FourPointBM` from `Research.HKOTriameterDH`) -/

/-- `FP(A,B,C)`: two of the three numbers are equal and the third is at most their common value
plus `2`. -/
def FP (A B C : ℕ) : Prop :=
  (A = B ∧ C ≤ A + 2) ∨ (A = C ∧ B ≤ A + 2) ∨ (B = C ∧ A ≤ B + 2)

/-- The four-point condition of Bandelt and Mulder for the path metric of `G`. -/
def FourPointBM {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v w x : V,
    FP (G.dist u v + G.dist w x) (G.dist u w + G.dist v x) (G.dist u x + G.dist v w)

/-- `FP` for integers (Lemma 2 is stated for integers). -/
def FPZ (A B C : ℤ) : Prop :=
  (A = B ∧ C ≤ A + 2) ∨ (A = C ∧ B ≤ A + 2) ∨ (B = C ∧ A ≤ B + 2)

/-- Condition (vii) of Bandelt–Mulder for three sums: at least two of them are equal. -/
def BMvii (A B C : ℕ) : Prop :=
  A = B ∨ A = C ∨ B = C

/-- The extra requirement of (viii): if the two smaller sums are equal, the largest exceeds them
by at most `2` (written for every choice of the two smaller ones). -/
def BMviiiExtra (A B C : ℕ) : Prop :=
  (A = B → A ≤ C → C ≤ A + 2) ∧ (A = C → A ≤ B → B ≤ A + 2) ∧ (B = C → B ≤ A → A ≤ B + 2)

/-- Problem 3 for graphs with the four-point condition (released statement). -/
def Problem3ClaimFP : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.Connected → FourPointBM G → Question3' G ∨ Question4 G

/-! ## 4. The integer grid (Section 3) -/

/-- `‖u - v‖₁ = ∑ᵢ |uᵢ - vᵢ|` for `u, v ∈ ℤ^k`, as a natural number. -/
def l1 {k : ℕ} (u v : Fin k → ℤ) : ℕ :=
  ∑ i, (u i - v i).natAbs

/-- `Γ(S)`: the graph on the finite set `S ⊆ ℤ^k` in which `u ~ v` iff `‖u - v‖₁ = 1`. -/
def gridGraph {k : ℕ} (S : Finset (Fin k → ℤ)) : SimpleGraph S where
  Adj u v := l1 (u : Fin k → ℤ) v = 1
  symm := ⟨fun u v h => by
    have e : l1 (v : Fin k → ℤ) u = l1 (u : Fin k → ℤ) v := by
      unfold l1
      exact Finset.sum_congr rfl fun i _ => by rw [← Int.natAbs_neg, neg_sub]
    exact e.trans h⟩
  loopless := ⟨fun u h => by simp [l1] at h⟩

/-- `med(a,b,c)`: the middle one of three integers. -/
def med3 (a b c : ℤ) : ℤ :=
  max (min a b) (min (max a b) c)

/-- `m(u,v,w)`: the coordinatewise median. -/
def medPt {k : ℕ} (u v w : Fin k → ℤ) : Fin k → ℤ :=
  fun i => med3 (u i) (v i) (w i)

/-- Condition (a) of Lemma 1: `d_{Γ(S)}(u,v) = ‖u - v‖₁` for all `u, v ∈ S`. -/
def GridA {k : ℕ} (S : Finset (Fin k → ℤ)) : Prop :=
  ∀ u v : S, (gridGraph S).dist u v = l1 (u : Fin k → ℤ) v

/-- Condition (b) of Lemma 1: `S` is closed under coordinatewise medians. -/
def GridB {k : ℕ} (S : Finset (Fin k → ℤ)) : Prop :=
  ∀ u v w : Fin k → ℤ, u ∈ S → v ∈ S → w ∈ S → medPt u v w ∈ S

/-- A list of integers is monotone (non-decreasing or non-increasing). -/
def MonotoneList (l : List ℤ) : Prop :=
  l.Pairwise (· ≤ ·) ∨ l.Pairwise (· ≥ ·)

/-- A monotone lattice path: a walk in `Γ(S)` along which every coordinate changes
monotonically. -/
def IsMonotoneWalk {k : ℕ} {S : Finset (Fin k → ℤ)} {u v : S} (p : (gridGraph S).Walk u v) :
    Prop :=
  ∀ i : Fin k, MonotoneList (p.support.map fun x => (x : Fin k → ℤ) i)

/-! ## 5. The concrete graphs -/

/-- Edge list of `G1` (verbatim). -/
def g1Edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 4), (0, 6), (1, 3), (2, 3), (2, 5), (4, 5), (4, 7), (6, 7)]

/-- The graph `G1` on `Fin 8` (verbatim). -/
def G1 : SimpleGraph (Fin 8) where
  Adj i j := (i.val, j.val) ∈ g1Edges ∨ (j.val, i.val) ∈ g1Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

/-- Edge list of `G2` (verbatim). -/
def g2Edges : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 6), (1, 2), (2, 5), (3, 4), (3, 5), (6, 7)]

/-- The graph `G2` on `Fin 8` (verbatim). -/
def G2 : SimpleGraph (Fin 8) where
  Adj i j := (i.val, j.val) ∈ g2Edges ∨ (j.val, i.val) ∈ g2Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

/-- HKO Figure 3, graph `G` (`y=0, m=1, a=2, b=3, c=4, x=5`), verbatim. -/
def f1gEdges : List (ℕ × ℕ) := [(0, 1), (1, 2), (1, 3), (1, 4), (2, 5), (3, 5), (4, 5)]

def F1G : SimpleGraph (Fin 6) where
  Adj i j := (i.val, j.val) ∈ f1gEdges ∨ (j.val, i.val) ∈ f1gEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

/-- HKO Figure 3, graph `H` (`a=0, b=1, c=2, x=3, m=4, y=5`), verbatim. -/
def f1hEdges : List (ℕ × ℕ) :=
  [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (4, 5)]

def F1H : SimpleGraph (Fin 6) where
  Adj i j := (i.val, j.val) ∈ f1hEdges ∨ (j.val, i.val) ∈ f1hEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

/-- `H₁₁` of Remark 5: edges `01, 02, 03, 05, 14, 16, 24, 27, 34, 38, 49, 5 10`. -/
def h11Edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 5), (1, 4), (1, 6), (2, 4), (2, 7), (3, 4), (3, 8), (4, 9),
    (5, 10)]

def H11 : SimpleGraph (Fin 11) where
  Adj i j := (i.val, j.val) ∈ h11Edges ∨ (j.val, i.val) ∈ h11Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

/-- HKO Figure 2 (their `fig-0`, Section 3.2): `x = 0`, `m₁ = 1`, `b = 2`, `m₃ = 3`, `m₄ = 4`,
`y = 5`, `t₁ = 6`, `a = 7`, `t₃ = 8`, `b₁ = 9`, `c = 10`, `b₃ = 11`. -/
def hkoFig2Edges : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 6), (0, 9), (9, 10), (10, 11), (6, 7), (7, 8),
    (8, 4), (11, 4)]

def HKOFig2 : SimpleGraph (Fin 12) where
  Adj i j := (i.val, j.val) ∈ hkoFig2Edges ∨ (j.val, i.val) ∈ hkoFig2Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

/-- The MathOverflow graph (answer 506536): the squares `s-u₁-a-u₂`, `s-v₁-b-v₂`, `s-v₁-x-w₁`,
`s-w₁-c-w₂`, with `s,u₁,u₂,a,v₁,v₂,b,x,w₁,w₂,c = 0,…,10`. -/
def moEdges : List (ℕ × ℕ) :=
  [(0, 1), (1, 3), (2, 3), (0, 2), (0, 4), (4, 6), (5, 6), (0, 5), (4, 7), (7, 8), (0, 8),
    (8, 10), (9, 10), (0, 9)]

def MOGraph : SimpleGraph (Fin 11) where
  Adj i j := (i.val, j.val) ∈ moEdges ∨ (j.val, i.val) ∈ moEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

/-- Grid positions of the vertices of `G1` (proof of Theorem A):
`3=(0,0), 2=(1,0), 5=(2,0), 1=(0,1), 0=(1,1), 4=(2,1), 6=(1,2), 7=(2,2)`. -/
def pos1 : Fin 8 → (Fin 2 → ℤ) :=
  ![![1, 1], ![0, 1], ![1, 0], ![0, 0], ![2, 1], ![2, 0], ![1, 2], ![2, 2]]

/-- `S₁ = {0,1,2}² ∖ {(0,2)}`. (`noncomputable` only because Mathlib's order instance on `ℤ`
used by `Finset.Icc` is; this affects code generation, not the meaning.) -/
noncomputable def S1 : Finset (Fin 2 → ℤ) :=
  ((Finset.Icc (0 : ℤ) 2 ×ˢ Finset.Icc (0 : ℤ) 2).image fun p => ![p.1, p.2]).erase ![0, 2]

/-- Grid positions of the vertices of `G2` (proof of Theorem B):
`7=(-2,0), 6=(-1,0), 0=(0,0), 2=(1,0), 1=(2,0), 3=(0,1), 5=(1,1), 4=(0,2)`. -/
def pos2 : Fin 8 → (Fin 2 → ℤ) :=
  ![![0, 0], ![2, 0], ![1, 0], ![0, 1], ![0, 2], ![1, 1], ![-1, 0], ![-2, 0]]

/-- `S₂ = R ∪ {(0,1), (1,1), (0,2)}` with the row `R = {(t,0) : -2 ≤ t ≤ 2}`. -/
noncomputable def S2 : Finset (Fin 2 → ℤ) :=
  (Finset.Icc (-2 : ℤ) 2).image (fun t => ![t, 0]) ∪ {![0, 1], ![1, 1], ![0, 2]}

/-! ## 6. Section 2: definitions and readings (tier 1) -/

/-- §2: on a finite connected graph, "eccentricity = diameter" is the same as "belongs to a
diametral pair". (Released: `HKOTriameter.isPeripheral_iff_isPeripheralPair`.) -/
def Sec2_peripheral_iff : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
    ∀ u : V, IsPeripheral G u ↔ IsPeripheralPair G u

/-- §2 (HKO Proposition 2.1, proved inline in the paper): `2 diam(G) ≤ tr(G) ≤ 3 diam(G)`, and
`d(x,y,z) ≥ 2 diam(G)` for every diametral pair `x, y` and every `z`. -/
def Sec2_bounds : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
    2 * G.diam ≤ triameter G ∧ triameter G ≤ 3 * G.diam ∧
      ∀ x y z : V, IsDiametral G x y → 2 * G.diam ≤ triDist G x y z

/-- §2, Readings: `d(u,u,v) = 2 d(u,v) ≤ 2D ≤ tr(G)`, with equality only if `tr(G) = 2D` and
`{u,v}` is diametral. -/
def Sec2_repeated : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → ∀ u v : V,
    triDist G u u v = 2 * G.dist u v ∧ triDist G u u v ≤ triameter G ∧
      (IsTriametral G u u v ↔ triameter G = 2 * G.diam ∧ IsDiametral G u v)

/-- §2, Readings: allowing repeated vertices changes nothing in (Q3) and (Q3′). -/
def Sec2_readings_Q3 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
    (Question3 G ↔ Question3Distinct G) ∧ (Question3' G ↔ Question3'Distinct G)

/-- §2, Readings: with at least three vertices the weak and strong readings of (Q4) agree, and
so do those of (Q4′). -/
def Sec2_readings_Q4 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → 3 ≤ Fintype.card V →
    (Question4 G ↔ Question4Strong G) ∧ (Question4' G ↔ Question4'Strong G)

/-- §2, Readings: (Q4) implies (Q4′). -/
def Sec2_Q4_imp_Q4' : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → Question4 G → Question4' G

/-- §2, Readings: (Q3) implies (Q3′). (Released: `HKOTriameter.question3'_of_question3`.) -/
def Sec2_Q3_imp_Q3' : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → Question3 G → Question3' G

/-- §2, Readings: the class reading of Problem 3 is refuted by HKO's Figure 3 graphs: neither
"all distance-hereditary graphs have (Q3′)" nor "all have (Q4)". -/
def Sec2_classReading : Prop :=
  ¬ (∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsDistanceHereditary G → Question3' G) ∧
    ¬ (∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsDistanceHereditary G → Question4 G)

/-- §2, Readings: the reading of the sentence before Problem 2 (Q3 for median graphs) is also
refuted (`G1 also lacks (Q3)`). -/
def Sec2_problem2_altReading : Prop :=
  ¬ (∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsMedian G → Question3 G)

/-! ## 7. Section 3: Lemma 1, the grid criterion, Theorems A and B (main parts) (tier 1) -/

/-- **Lemma 1.** For a finite nonempty `S ⊆ ℤ^k` with (a) and (b), `Γ(S)` is a median graph, the
median of `u, v, w` is `m(u,v,w)`, and `d(u,v,w) = 2 ∑ᵢ (max − min)`.
(Nonemptiness is added: Mathlib's `Connected` requires a vertex; the paper's graphs are
nonempty.) -/
def Lemma1 : Prop :=
  ∀ (k : ℕ) (S : Finset (Fin k → ℤ)), S.Nonempty → GridA S → GridB S →
    IsMedian (gridGraph S) ∧
      (∀ u v w x : S,
        (InInterval (gridGraph S) u v x ∧ InInterval (gridGraph S) u w x ∧
            InInterval (gridGraph S) v w x) ↔ (x : Fin k → ℤ) = medPt u v w) ∧
      ∀ u v w : S, (triDist (gridGraph S) u v w : ℤ) =
        2 * ∑ i, (max (max (u.1 i) (v.1 i)) (w.1 i) - min (min (u.1 i) (v.1 i)) (w.1 i))

/-- §3, after Lemma 1: condition (a) holds if any two points of `S` are joined by a monotone
lattice path in `S`. -/
def Sec3_monotonePath : Prop :=
  ∀ (k : ℕ) (S : Finset (Fin k → ℤ)),
    (∀ u v : S, ∃ p : (gridGraph S).Walk u v, IsMonotoneWalk p) → GridA S

/-- Proof of Theorem A: `pos1` is a bijection of `Fin 8` onto `S₁`, the pairs at `ℓ¹`-distance
`1` are exactly the edges of `G1` (so `G1 ≅ Γ(S₁)`), and `S₁` satisfies (a) and (b). -/
def TheoremA_grid : Prop :=
  Function.Injective pos1 ∧ (∀ s, s ∈ S1 ↔ ∃ i, pos1 i = s) ∧
    (∀ i j, G1.Adj i j ↔ l1 (pos1 i) (pos1 j) = 1) ∧ Nonempty (G1 ≃g gridGraph S1) ∧
    GridA S1 ∧ GridB S1

/-- **Theorem A** (all but the last sentence): `G1` is median, `diam = 4`, `tr = 8`, the only
peripheral vertices are `3` and `7`, `{1,5,6}` is triametral, so `G1` lacks (Q3′), and
Problem 1 has a negative answer (with either definition of "peripheral"). -/
def TheoremA_i : Prop :=
  IsMedian G1 ∧ G1.diam = 4 ∧ triameter G1 = 8 ∧
    (∀ u, IsPeripheral G1 u ↔ u = 3 ∨ u = 7) ∧ IsTriametral G1 1 5 6 ∧
    ¬ Question3' G1 ∧ ¬ Question3'Pair G1 ∧ ¬ Question3'Distinct G1 ∧ ¬ Problem1Claim ∧
    ¬ Problem1ClaimPair

/-- Proof of Theorem A, further facts: the only diametral pair is `{3,7}`; `d(1,5) = 3`,
`d(1,6) = 2`, `d(5,6) = 3`; `G1` lacks (Q3); `G1` has (Q4) (as `tr = 2 diam`), in both readings.
(Section 8 also uses "`G1` has (Q4)".) -/
def TheoremA_ii : Prop :=
  (∀ u v, IsDiametral G1 u v ↔ (u = 3 ∧ v = 7) ∨ (u = 7 ∧ v = 3)) ∧
    G1.dist 1 5 = 3 ∧ G1.dist 1 6 = 2 ∧ G1.dist 5 6 = 3 ∧ ¬ Question3 G1 ∧
    triameter G1 = 2 * G1.diam ∧ Question4 G1 ∧ Question4Strong G1

/-- Proof of Theorem B: `pos2` is a bijection of `Fin 8` onto `S₂`, the pairs at `ℓ¹`-distance
`1` are exactly the edges of `G2`, and `S₂` satisfies (a) and (b). -/
def TheoremB_grid : Prop :=
  Function.Injective pos2 ∧ (∀ s, s ∈ S2 ↔ ∃ i, pos2 i = s) ∧
    (∀ i j, G2.Adj i j ↔ l1 (pos2 i) (pos2 j) = 1) ∧ Nonempty (G2 ≃g gridGraph S2) ∧
    GridA S2 ∧ GridB S2

/-- **Theorem B** (all but the last sentence): `G2` is median and distance-hereditary,
`diam = 4`, `tr = 12`, and `{1,4,7}` is its only triametral triple (every triametral ordered
triple is a permutation of `1, 4, 7`). -/
def TheoremB_i : Prop :=
  IsMedian G2 ∧ IsDistanceHereditary G2 ∧ G2.diam = 4 ∧ triameter G2 = 12 ∧
    ∀ a b c, IsTriametral G2 a b c ↔ ({a, b, c} : Finset (Fin 8)) = {1, 4, 7}

/-- **Theorem B**, continued: `1, 4, 7` are pairwise at distance `4`; `{5,7}` is diametral and
does not extend (no `z` at all); `5` is peripheral and lies in no triametral triple; so `G2` has
neither (Q4) nor (Q4′), in both readings; `G2` has (Q3); and Problem 2 and its weak form have
negative answers. -/
def TheoremB_ii : Prop :=
  G2.dist 1 4 = 4 ∧ G2.dist 1 7 = 4 ∧ G2.dist 4 7 = 4 ∧
    IsDiametral G2 5 7 ∧ (∀ z, ¬ IsTriametral G2 5 7 z) ∧ IsPeripheral G2 5 ∧
    (∀ y z, ¬ IsTriametral G2 5 y z) ∧
    ¬ Question4 G2 ∧ ¬ Question4' G2 ∧ ¬ Question4Strong G2 ∧ ¬ Question4'Strong G2 ∧
    Question3 G2 ∧ ¬ Problem2Claim ∧ ¬ Problem2ClaimWeak

/-- §3, after Theorem B: (Q4) fails even for a graph that is both median and
distance-hereditary. -/
def Sec3_medianDH_noQ4 : Prop :=
  ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
    IsMedian G ∧ IsDistanceHereditary G ∧ ¬ Question4 G

/-- §3, after Theorem B: in a distance-hereditary graph (Q4) can fail only if (Q3) holds. -/
def Sec3_DH_noQ4_imp_Q3 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsDistanceHereditary G →
    ¬ Question4 G → Question3 G

/-- §3, after Theorem B: the MathOverflow example is not distance-hereditary: `b, v₂, s, w₁, x`
(`6, 5, 0, 8, 7`) induce a path of length 4, while `d(b,x) = 2`. -/
def Sec3_MO_notDH : Prop :=
  (∀ i j : Fin 5, MOGraph.Adj (![6, 5, 0, 8, 7] i) (![6, 5, 0, 8, 7] j) ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val)) ∧
    MOGraph.dist 6 7 = 2 ∧ ¬ IsDistanceHereditary MOGraph

/-! ## 8. Section 4: the last sentences of Theorems A and B (tier 1) -/

/-- **Theorem A**, last sentence, part 1: every median graph with at most seven vertices has
(Q3′). -/
def TheoremA_min : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ 7 → IsMedian G → Question3' G

/-- **Theorem A**, last sentence, part 2: up to isomorphism, `G1` is the only median graph with
eight vertices that lacks (Q3′). -/
def TheoremA_unique : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V = 8 → IsMedian G →
    ¬ Question3' G → Nonempty (G ≃g G1)

/-- **Theorem B**, last sentence, part 1: every median graph with at most seven vertices has
(Q4); hence also (Q4′) (§4). -/
def TheoremB_min : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ 7 → IsMedian G →
    Question4 G ∧ Question4' G

/-- **Theorem B**, last sentence, part 2: up to isomorphism, `G2` is the only median graph with
eight vertices that lacks (Q4), and the only one that lacks (Q4′). -/
def TheoremB_unique : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V = 8 → IsMedian G →
    (¬ Question4 G → Nonempty (G ≃g G2)) ∧ (¬ Question4' G → Nonempty (G ≃g G2))

/-- §4: a median graph has no triangle. -/
def Sec4_median_triangleFree : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsMedian G → G.CliqueFree 3

/-- §4: every connected graph with at least two vertices has a vertex whose removal leaves it
connected (Mathlib: `Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`). -/
def Sec4_nonCutVertex : Prop :=
  ∀ (V : Type) [Fintype V] [Nontrivial V] (G : SimpleGraph V), G.Connected →
    ∃ v : V, (G.induce {v}ᶜ).Connected

/-- §4: every median graph with eight vertices arises from a connected triangle-free graph with
seven vertices by adding a vertex adjacent to a nonempty independent set. -/
def Sec4_reduction : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), Fintype.card V = 8 → IsMedian G →
    ∃ v : V, (G.induce {v}ᶜ).Connected ∧ (G.induce {v}ᶜ).CliqueFree 3 ∧ (∃ w, G.Adj v w) ∧
      ∀ a b, G.Adj v a → G.Adj v b → ¬ G.Adj a b

/-! ## 9. Section 5: the four-point condition, Lemma 2, Proposition 3, Theorem C (tier 1) -/

/-- §5: `FP` is symmetric in its three arguments. The paper defines `FP` for integers, so the symmetry
is stated for `ℤ` (`FPZ`, used in Lemma 2) as well as for `ℕ` (`FP`, used for distance sums). -/
def Sec5_FP_symm : Prop :=
  (∀ A B C : ℕ, (FP A B C ↔ FP B A C) ∧ (FP A B C ↔ FP A C B) ∧ (FP A B C ↔ FP C B A)) ∧
    ∀ A B C : ℤ, (FPZ A B C ↔ FPZ B A C) ∧ (FPZ A B C ↔ FPZ A C B) ∧ (FPZ A B C ↔ FPZ C B A)

/-- §5: three sums satisfy `FP` exactly when they satisfy the requirements of (viii), i.e. (vii)
together with the bound on the largest sum. -/
def Sec5_FP_iff_viii : Prop :=
  ∀ A B C : ℕ, FP A B C ↔ BMvii A B C ∧ BMviiiExtra A B C

/-- **Cited theorem** (Bandelt–Mulder 1986, Theorem 2, (i) ⇒ (viii)): every finite connected
distance-hereditary graph satisfies the four-point condition. Not in Mathlib; must be formalized. -/
def BandeltMulder_DH_fourPoint : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsDistanceHereditary G → FourPointBM G

/-- **Cited theorem** (Bandelt–Mulder 1986, Theorem 1, easy direction, used for `G2` and `H₁₁`):
attaching a pendant vertex or adding a twin preserves distance-heredity. Stated for a connected
graph `G` and a vertex `v` such that `G − v` is distance-hereditary. (Connectedness of `G` is
needed: two isolated vertices are false twins.) -/
def BandeltMulder_extension : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (v : V), G.Connected →
    (IsPendant G v ∨ ∃ t, AreTwins G v t) → IsDistanceHereditary (G.induce {v}ᶜ) →
    IsDistanceHereditary G

/-- **Lemma 2** (over the integers; the released `HKOTriameter.core` is the natural-number
case). Each condition (E), (F) is stated once per unordered pair; the paper states them for
ordered pairs, which is equivalent because `FP` is symmetric, so this is at least as strong. -/
def Lemma2 : Prop :=
  ∀ D eab eac ebc pa pb pc qa qb qc : ℤ,
    eab ≤ D - 1 → eac ≤ D - 1 → ebc ≤ D - 1 →
    FPZ (D + eab) (pa + qb) (pb + qa) → FPZ (D + eac) (pa + qc) (pc + qa) →
    FPZ (D + ebc) (pb + qc) (pc + qb) →
    D + pa + qa ≤ eab + eac + ebc - 1 → D + pb + qb ≤ eab + eac + ebc - 1 →
    D + pc + qc ≤ eab + eac + ebc - 1 → False

/-- **Proposition 3.** In a finite connected graph with the four-point condition, for a
diametral pair `x, y` and vertices `a, b, c` with `d(a,b), d(a,c), d(b,c) < diam(G)`,
`max {d(a,x,y), d(b,x,y), d(c,x,y)} ≥ d(a,b,c)`. -/
def Proposition3 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → FourPointBM G →
    ∀ x y : V, IsDiametral G x y → ∀ a b c : V,
      G.dist a b < G.diam → G.dist a c < G.diam → G.dist b c < G.diam →
        triDist G a b c ≤ max (max (triDist G a x y) (triDist G b x y)) (triDist G c x y)

/-- The displayed equation of Theorem C, for a class of graphs given by a predicate. -/
def TheoremCEquation (V : Type) [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ a b c : V, IsTriametral G a b c →
    ¬ IsDiametral G a b → ¬ IsDiametral G a c → ¬ IsDiametral G b c →
    ∀ x y : V, IsDiametral G x y →
      max (max (triDist G a x y) (triDist G b x y)) (triDist G c x y) = triameter G

/-- **Theorem C**, the displayed equation, for connected distance-hereditary graphs. -/
def TheoremC_i : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsDistanceHereditary G → TheoremCEquation V G

/-- **Theorem C**, consequences: every connected distance-hereditary graph has (Q3) or (Q4), hence
(Q3′) or (Q4) (Problem 3, per-graph reading, positive); also (Q3) or (Q4) in the strong reading;
and (Q3′) or (Q4′) (§2, last sentence). -/
def TheoremC_ii : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsDistanceHereditary G →
    (Question3 G ∨ Question4 G) ∧ (Question3' G ∨ Question4 G) ∧
      (Question3 G ∨ Question4Strong G) ∧ (Question3' G ∨ Question4' G)

/-- §1 and §5: Theorem C holds for every finite connected graph with the four-point condition
(equation, (Q3) or (Q4) in both readings, and (Q3′) or (Q4)). The weak-reading disjunctions are
released (`HKOTriameter.question3_or_question4`, `HKOTriameter.problem3ClaimFP`). -/
def TheoremC_FP : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → FourPointBM G →
    TheoremCEquation V G ∧ (Question3 G ∨ Question4 G) ∧ (Question3 G ∨ Question4Strong G) ∧
      (Question3' G ∨ Question4 G)

/-! ## 10. Remarks 4 and 5, Sections 6 and 8 (tier 1) -/

/-- **Remark 4 (1)**: HKO's `G` is distance-hereditary and lacks (Q3′); HKO's `H` and `G2` are
distance-hereditary and lack (Q4). -/
def Remark4_i : Prop :=
  IsDistanceHereditary F1G ∧ ¬ Question3' F1G ∧ IsDistanceHereditary F1H ∧ ¬ Question4 F1H ∧
    IsDistanceHereditary G2 ∧ ¬ Question4 G2

/-- **Remark 4 (2)**: in `H` (`diam 2`, `tr 6`) the only triametral triple is `{a,b,c}`, with
pairwise distances `2`, and the diametral pair `{x,y}` does not extend. -/
def Remark4_ii : Prop :=
  F1H.diam = 2 ∧ triameter F1H = 6 ∧
    (∀ u v w, IsTriametral F1H u v w ↔ ({u, v, w} : Finset (Fin 6)) = {0, 1, 2}) ∧
    F1H.dist 0 1 = 2 ∧ F1H.dist 0 2 = 2 ∧ F1H.dist 1 2 = 2 ∧
    IsDiametral F1H 3 5 ∧ ∀ z, ¬ IsTriametral F1H 3 5 z

/-- **Remark 4 (3)**: HKO's Figure 2 graph has `diam 5`, `tr 12`, the only triametral triple
`{a,b,c}` with pairwise distances `4`, the only diametral pair `{x,y}`, which does not extend,
`x, y` are its only peripheral vertices, and it has none of (Q3), (Q3′), (Q4). -/
def Remark4_iii : Prop :=
  HKOFig2.diam = 5 ∧ triameter HKOFig2 = 12 ∧
    (∀ u v w, IsTriametral HKOFig2 u v w ↔ ({u, v, w} : Finset (Fin 12)) = {7, 2, 10}) ∧
    HKOFig2.dist 7 2 = 4 ∧ HKOFig2.dist 7 10 = 4 ∧ HKOFig2.dist 2 10 = 4 ∧
    (∀ u v, IsDiametral HKOFig2 u v ↔ (u = 0 ∧ v = 5) ∨ (u = 5 ∧ v = 0)) ∧
    (∀ z, ¬ IsTriametral HKOFig2 0 5 z) ∧ (∀ u, IsPeripheral HKOFig2 u ↔ u = 0 ∨ u = 5) ∧
    ¬ Question3 HKOFig2 ∧ ¬ Question3' HKOFig2 ∧ ¬ Question4 HKOFig2

/-- **Remark 5**, first sentence: (Q4) holds (in both readings, the strong one for at least three
vertices) when `tr(G) = 2 diam(G)`. -/
def Remark5_i : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → triameter G = 2 * G.diam →
    Question4 G ∧ (3 ≤ Fintype.card V → Question4Strong G)

/-- **Remark 5**: `H₁₁` is distance-hereditary; its only diametral pair is `{9,10}`, at distance
`5`; `6, 7, 8` are pairwise at distance `4`; `tr(H₁₁) = 12 > 10`; `{6,7,8}` is a triametral
triple without a peripheral vertex; (Q4) holds, and `{9,10}` extends by each of `6, 7, 8`, e.g.
`d(9,10,6) = 5 + 3 + 4 = 12`. -/
def Remark5_ii : Prop :=
  IsDistanceHereditary H11 ∧
    (∀ u v, IsDiametral H11 u v ↔ (u = 9 ∧ v = 10) ∨ (u = 10 ∧ v = 9)) ∧ H11.diam = 5 ∧
    H11.dist 6 7 = 4 ∧ H11.dist 6 8 = 4 ∧ H11.dist 7 8 = 4 ∧
    triameter H11 = 12 ∧ 2 * H11.diam < triameter H11 ∧ IsTriametral H11 6 7 8 ∧
    ¬ IsPeripheral H11 6 ∧ ¬ IsPeripheral H11 7 ∧ ¬ IsPeripheral H11 8 ∧ ¬ Question3' H11 ∧
    Question4 H11 ∧ IsTriametral H11 9 10 6 ∧ IsTriametral H11 9 10 7 ∧ IsTriametral H11 9 10 8 ∧
    H11.dist 9 10 = 5 ∧ H11.dist 9 6 = 3 ∧ H11.dist 10 6 = 4

/-- **Remark 5**: distance-hereditary graphs with `tr(G) > 2 diam(G)` need not have (Q3′). -/
def Remark5_iii : Prop :=
  ¬ ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsDistanceHereditary G →
    2 * G.diam < triameter G → Question3' G

/-- §6, last sentence (a test from the definition): `G2`, `H₁₁` and HKO's Figure 3 graphs are
distance-hereditary; `G1` and HKO's Figure 2 graph are not. -/
def Sec6_DHtests : Prop :=
  IsDistanceHereditary G2 ∧ IsDistanceHereditary H11 ∧ IsDistanceHereditary F1G ∧
    IsDistanceHereditary F1H ∧ ¬ IsDistanceHereditary G1 ∧ ¬ IsDistanceHereditary HKOFig2

/-- §8: `G1` has (Q4) and `G2` has (Q3′), so the examples leave the median analogue of Problem 3
open. -/
def Sec8_open : Prop :=
  Question4 G1 ∧ Question3' G2

/-- Released facts about the four-point condition (sanity checks of `HKOTriameterDH`): HKO's
Figure 3 graphs and `G2` satisfy it, `G1` does not, and HKO's `G` is not a median graph
(footnote in §1). -/
def Released_fourPoint_facts : Prop :=
  FourPointBM F1G ∧ FourPointBM F1H ∧ FourPointBM G2 ∧ ¬ FourPointBM G1 ∧ ¬ IsMedian F1G

/-! ## 11. Tier 2: counts reported in Section 4 -/

/-- "There are exactly `m` isomorphism classes of graphs on `n` vertices with property `P`":
`m` pairwise non-isomorphic representatives on `Fin n` with `P`, and every graph on any
`n`-element type with `P` is isomorphic to one of them. -/
def ClassCount (P : ∀ {W : Type}, SimpleGraph W → Prop) (n m : ℕ) : Prop :=
  ∃ L : Fin m → SimpleGraph (Fin n),
    (∀ i, P (L i)) ∧ (∀ i j, Nonempty (L i ≃g L j) → i = j) ∧
      ∀ (W : Type) [Fintype W] (G : SimpleGraph W), Fintype.card W = n → P G →
        ∃ i, Nonempty (G ≃g L i)

/-- §4: the numbers of median graphs up to isomorphism with `n = 1, …, 8` vertices are
`1, 1, 1, 3, 4, 11, 23, 69` (OEIS A292623). -/
def Sec4_count_median : Prop :=
  ClassCount (fun G => IsMedian G) 1 1 ∧ ClassCount (fun G => IsMedian G) 2 1 ∧
    ClassCount (fun G => IsMedian G) 3 1 ∧ ClassCount (fun G => IsMedian G) 4 3 ∧
    ClassCount (fun G => IsMedian G) 5 4 ∧ ClassCount (fun G => IsMedian G) 6 11 ∧
    ClassCount (fun G => IsMedian G) 7 23 ∧ ClassCount (fun G => IsMedian G) 8 69

/-- §4: there are `59` connected triangle-free graphs with seven vertices, up to isomorphism. -/
def Sec4_count_triangleFree7 : Prop :=
  ClassCount (fun G => G.Connected ∧ G.CliqueFree 3) 7 59

/-- §4: the second program forms `1,857` graphs: over the `59` connected triangle-free graphs with
seven vertices (up to isomorphism), the numbers of nonempty independent sets add up to `1,857`
(each such set gives one augmented graph). Stated with a list of `59` pairwise non-isomorphic
representatives that covers all such graphs; the sum does not depend on the choice, since the
number of nonempty independent sets is an isomorphism invariant. (Text of the review, M1.) -/
def Sec4_count_candidates : Prop :=
  ∃ L : Fin 59 → SimpleGraph (Fin 7),
    (∀ i, (L i).Connected ∧ (L i).CliqueFree 3) ∧ (∀ i j, Nonempty (L i ≃g L j) → i = j) ∧
      (∀ (W : Type) [Fintype W] (G : SimpleGraph W), Fintype.card W = 7 → G.Connected →
        G.CliqueFree 3 → ∃ i, Nonempty (G ≃g L i)) ∧
      ∑ i, Nat.card {s : Set (Fin 7) // s.Nonempty ∧ (L i).IsIndepSet s} = 1857

/-- §4: there are `1,008,904` labelled median graphs on `{0,…,7}`; exactly `20,160` of them lack
(Q3′) and exactly `20,160` lack (Q4). -/
def Sec4_count_labelled : Prop :=
  Nat.card {G : SimpleGraph (Fin 8) // IsMedian G} = 1008904 ∧
    Nat.card {G : SimpleGraph (Fin 8) // IsMedian G ∧ ¬ Question3' G} = 20160 ∧
    Nat.card {G : SimpleGraph (Fin 8) // IsMedian G ∧ ¬ Question4 G} = 20160

/-- §4: each of `G1` and `G2` has exactly two automorphisms. -/
def Sec4_aut : Prop :=
  Nat.card (G1 ≃g G1) = 2 ∧ Nat.card (G2 ≃g G2) = 2

end BackfillPaper4.Challenge
