import Mathlib

/-!
# Paper 3 back-fill: challenge statements (version 2)

Paper: H. Dong, "A negative answer to a question of Carenini on almost independent sets in
regular graphs" (`papers/carenini-almost-independent/note.tex`, release v1.3.0).

This file contains **definitions and statements only** (every statement is a `def ... : Prop`).
It imports only Mathlib. Nothing here is proved. After independent review it is frozen by
SHA-256; the proofs go into separate modules, and `Check.lean` will contain
`theorem check_X : Challenge.X := ...` for every `X` below.

## Conventions (see `work/lean-backfill/paper3/STATEMENTS.md` for the full table)

* Trust surface: Mathlib definitions wherever they exist. The custom definitions the reader must
  trust are listed in `STATEMENTS.md` ("Definitions the reader must trust") and tested in
  `ChallengeTests.lean`.
* All graphs are Mathlib `SimpleGraph`s (finite, simple, loopless); "a graph on `n` vertices" is
  a graph on an arbitrary `V : Type` with `[Fintype V]` and `Fintype.card V = n`.
* "`d`-regular" is Mathlib's `SimpleGraph.IsRegularOfDegree d`.
* `edgesIn`, `iCount`, `iGamma` and `CareniniQuestion` are verbatim copies of the definitions in
  the released module `Research.Carenini` (v1.3.0). `KddUnion` is now built from Mathlib's box
  product (`copies m G = ⊥ □ G`); it has the same adjacency as `Carenini.KddUnion` up to a
  logical equivalence, so linking the five released results needs a one-line isomorphism.
* `m G` (disjoint union of `m` copies) is `copies m G = (⊥ : SimpleGraph (Fin m)) □ G`;
  `G ∪ F` is Mathlib's disjoint sum `G ⊕g F` on `V ⊕ W`; `K_d □ K_2` is Mathlib's box product of
  complete graphs; `C_n` is Mathlib's `cycleGraph n`; triangles are Mathlib's `cliqueFinset 3`;
  bipartite is Mathlib's `IsBipartite` (= `Colorable 2`); connected is Mathlib's `Connected`;
  a 2-switch is Mathlib's `deleteEdges` followed by `⊔ fromEdgeSet`.
* Polynomials `P_G`, `P_d`, `W_{αβ}`, `D` have integer coefficients; real values are taken with
  `Polynomial.aeval` (`evalR`).
* The paper's vertex labels `x_1, x_2, …` become arbitrary distinct elements of `Fin d`; every
  statement about `S_d` or `H_d` quantifies over **all** admissible choices (stronger than one
  fixed choice).
* "`liminf_m (1/m) log a_m ≥ L`" is stated as `∀ ε > 0, ∀ᶠ m, exp (m (L - ε)) ≤ a_m`
  (equivalent, and free of the `log 0 = 0` convention).
* Lemma 8 is stated in Mathlib's probability language (`PMF`, `iIndepFun`, `HasLaw`, Bochner
  integral); no custom probability definitions.
* Infima over `q ∈ (0,1]` or `λ ≥ 0` are `⨅` in `ℝ`; the separate statements `*_bddBelow` say that
  these families are bounded below, so the `⨅` is the true infimum and not a junk value.
* These statements were written in 2026-09 **after** the paper and its proofs (back-fill); the
  disclosure of any corrected version must say so.

## Tiers

* Tier 0: facts stated in §3 (Preliminaries) and §9 (Formal verification) of the paper.
* Tier 1: the numbered and named results (Lemmas 1, 3, 6, 7, 8; Propositions 2, C;
  Theorems A, B, B′, D; Corollary 5; Remark 4), with `WSymm` and the two `*_bddBelow`
  well-definedness statements.
* Tier C: cited theorems the proofs rely on (Carenini's Proposition 2.1 with fugacity 1, via
  Sah–Sawhney–Stoner–Zhao; the Kahn–Zhao theorem). The 2-switch theorem cited in §8
  (`TwoSwitchConnected`) is stated with the Tier 3 statements.
* Tier 2: mathematical claims made in the abstract, the introduction, the "Readings" table and
  Remarks 9–12.
* Tier 3: the computational claims of §8 (Table 2, class counts, and the Theorem D numerics).

## Version 2

Version 1 (SHA-256 `5cf68b68181d0528bab5ebc8a2b18abe29b0409b1f40d23f3176d3ed45873163`, 58
statements) was reviewed twice and accepted as faithful; no proofs were written against it.
Version 2 changes only the scope, following the rule that every claim of the corrected paper is
proved in Lean and claims that are not proved are deleted from the paper:

* deleted: the second conjunct of `Remark10d` (the normal approximation
  `i_{1/8}(G) = (1/2 + O(n^{-1/4})) 2^n`, which rests on Stein's method) and, with it, the
  case `γ = 1/8` of `ReadingR6` (now `γ = 0` or `γ > 1/8`); the corrected paper drops these
  claims;
* deleted: the count `19355` of labelled 4-regular graphs on 8 vertices in `LabelledCounts` (a
  statement about a referee's cross-check; the corrected paper drops it);
* added: `Question13` (the question as one statement; a definition, like `CareniniQuestion`,
  not a statement to prove) and `AnswerNegative` (its negation; review item M1);
* added: the values `tStar 6 3 = 1`, `gammaStar 6 3 = 1/18` as a conjunct of `GammaStarScope`
  (review item M2);
* added: `LowGammaExamples` (§1, "Scope": every counterexample of the paper with `γ ≤ 1/8` has
  `γ d < 1`);
* header: the Tier C paragraph now says where `TwoSwitchConnected` is stated (cosmetic item 7 of
  the review of version 1).

Every other statement and every definition is unchanged. Version 2 has 60 statements.
-/

set_option autoImplicit false

namespace BackfillPaper3.Challenge

open Finset SimpleGraph Polynomial Filter Topology

/-! ## §0. Counting vertex sets by the number of edges they span -/

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `e_G(A)`: the number of edges of `G` with both ends in `A`. (Verbatim `Carenini.edgesIn`.) -/
def edgesIn (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : ℕ :=
  #(G.edgeFinset.filter (· ∈ A.sym2))

/-- `N_{≤t}(G) = #{A ⊆ V : e_G(A) ≤ t}` for `t : ℕ`. (Verbatim `Carenini.iCount`.) -/
def iCount (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) : ℕ :=
  #((univ : Finset (Finset V)).filter (fun A => edgesIn G A ≤ t))

/-- `N_{≤t}(G)` for an integer threshold `t` (Lemma 1 and Proposition 2 use integers; for
`t < 0` it is `0`). -/
def NleZ (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℤ) : ℕ :=
  #((univ : Finset (Finset V)).filter (fun A => (edgesIn G A : ℤ) ≤ t))

open Classical in
/-- Carenini's `i_γ(G) = #{A ⊆ V : e_G(A) ≤ γ d n}` with real `γ` and `n = |V|`.
(Verbatim `Carenini.iGamma`.) -/
noncomputable def iGamma (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (γ : ℝ) : ℕ :=
  #((univ : Finset (Finset V)).filter
    (fun A => ((edgesIn G A : ℕ) : ℝ) ≤ γ * d * (Fintype.card V : ℝ)))

/-- `∂(S)`: the number of edges of `G` meeting `S` (the union of Mathlib's incidence sets of the
vertices of `S`). -/
def boundary (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  #(S.biUnion fun v => G.incidenceFinset v)

/-- The edge polynomial `P_G(z) = ∑_{A ⊆ V} z^{e_G(A)} = ∑_s N_s(G) z^s`. -/
noncomputable def edgePoly (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ[X] :=
  ∑ A : Finset V, X ^ edgesIn G A

/-- `T(G)`: the number of triangles of `G`. -/
def triangles (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  #(G.cliqueFinset 3)

/-- `Q(G)` for a `d`-regular `G`: the number of 4-sets spanning at least `d + 2` edges plus the
number of 5-sets spanning at least `2d + 2` edges. -/
def Qcount (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : ℕ :=
  #((univ : Finset (Finset V)).filter (fun S => #S = 4 ∧ d + 2 ≤ edgesIn G S)) +
    #((univ : Finset (Finset V)).filter (fun S => #S = 5 ∧ 2 * d + 2 ≤ edgesIn G S))

/-- `c₄(G)`: the number of connected components of `G` isomorphic to `C₄`. -/
noncomputable def c4 (G : SimpleGraph V) : ℕ :=
  Nat.card {c : G.ConnectedComponent // Nonempty (G.induce c.supp ≃g cycleGraph 4)}

end Counting

/-- Real value of an integer polynomial. -/
noncomputable def evalR (p : ℤ[X]) (q : ℝ) : ℝ :=
  Polynomial.aeval q p

/-! ## §1. Graphs -/

/-- `K_{d,d}`: Mathlib's complete bipartite graph on `Fin d ⊕ Fin d` (sides `X = inl`,
`Y = inr`). -/
abbrev Kdd (d : ℕ) : SimpleGraph (Fin d ⊕ Fin d) :=
  completeBipartiteGraph (Fin d) (Fin d)

instance (d : ℕ) : DecidableRel (completeBipartiteGraph (Fin d) (Fin d)).Adj := fun x y =>
  inferInstanceAs
    (Decidable (x.isLeft = true ∧ y.isRight = true ∨ x.isRight = true ∧ y.isLeft = true))

/-- `m G`: the disjoint union of `m` copies of `G`, on `Fin m × W`, as Mathlib's box product of
the empty graph on `Fin m` with `G`: `(i, x) ~ (j, y)` iff `i = j` and `x ~ y`. -/
abbrev copies (m : ℕ) {W : Type*} (G : SimpleGraph W) : SimpleGraph (Fin m × W) :=
  (⊥ : SimpleGraph (Fin m)) □ G

instance (m : ℕ) {W : Type*} [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj] :
    DecidableRel (copies m G).Adj := fun x y =>
  inferInstanceAs (Decidable ((⊥ : SimpleGraph (Fin m)).Adj x.1 y.1 ∧ x.2 = y.2 ∨
    G.Adj x.2 y.2 ∧ x.1 = y.1))

/-- `m K_{d,d}` on `Fin m × (Fin d ⊕ Fin d)`. It has the same adjacency relation as the released
`Carenini.KddUnion m d` (`x.1 = y.1 ∧ K_{d,d}.Adj x.2 y.2`), up to the logical equivalence
`(⊥.Adj i j ∧ x = y) ∨ (K.Adj x y ∧ i = j) ↔ (i = j ∧ K.Adj x y)`. -/
abbrev KddUnion (m d : ℕ) : SimpleGraph (Fin m × (Fin d ⊕ Fin d)) :=
  copies m (Kdd d)

instance {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj]
    [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj
  | .inl u, .inl v => inferInstanceAs (Decidable (G.Adj u v))
  | .inr u, .inr v => inferInstanceAs (Decidable (H.Adj u v))
  | .inl _, .inr _ => isFalse (by simp)
  | .inr _, .inl _ => isFalse (by simp)

instance {α β : Type*} [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G □ H).Adj := fun x y =>
  inferInstanceAs (Decidable (G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1))

/-- The 2-switch of `G`: delete the edges `u₁w₁` and `u₂w₂` and add the edges `u₁w₂` and `u₂w₁`,
with Mathlib's `deleteEdges` and `fromEdgeSet` (which never creates loops). -/
abbrev twoSwitch {V : Type*} (G : SimpleGraph V) (u₁ w₁ u₂ w₂ : V) : SimpleGraph V :=
  G.deleteEdges {s(u₁, w₁), s(u₂, w₂)} ⊔ SimpleGraph.fromEdgeSet {s(u₁, w₂), s(u₂, w₁)}

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (u₁ w₁ u₂ w₂ : V) :
    DecidableRel (twoSwitch G u₁ w₁ u₂ w₂).Adj := fun x y =>
  decidable_of_iff
    ((G.Adj x y ∧ ¬ (s(x, y) = s(u₁, w₁) ∨ s(x, y) = s(u₂, w₂))) ∨
      ((s(x, y) = s(u₁, w₂) ∨ s(x, y) = s(u₂, w₁)) ∧ x ≠ y))
    (by simp [twoSwitch])

/-- `S_d` (Theorem B): from `K_{d,d}` with `x₁ = inl a₁`, `x₂ = inl a₂`, `y₁ = inr b₁`,
`y₂ = inr b₂`, delete `x₁y₁`, `x₂y₂` and add `x₁x₂`, `y₁y₂`. (As a 2-switch:
`u₁ = x₁, w₁ = y₁, u₂ = y₂, w₂ = x₂`.) Meaningful for `a₁ ≠ a₂`, `b₁ ≠ b₂`. -/
abbrev Sd (d : ℕ) (a₁ a₂ b₁ b₂ : Fin d) : SimpleGraph (Fin d ⊕ Fin d) :=
  twoSwitch (Kdd d) (.inl a₁) (.inr b₁) (.inr b₂) (.inl a₂)

/-- `H_d` (Theorem B′): two copies `k = 0, 1` of `K_{d,d}` (`X_k = {k} × inl`, `Y_k = {k} × inr`),
`u_k = (k, inl a_k)`, `w_k = (k, inr b_k)`; delete `u₁w₁`, `u₂w₂`, add `u₁w₂`, `u₂w₁`. -/
abbrev Hd (d : ℕ) (a₁ b₁ a₂ b₂ : Fin d) : SimpleGraph (Fin 2 × (Fin d ⊕ Fin d)) :=
  twoSwitch (KddUnion 2 d) (0, .inl a₁) (0, .inr b₁) (1, .inl a₂) (1, .inr b₂)

instance (d : ℕ) (a₁ b₁ a₂ b₂ : Fin d) : DecidableRel (Hd d a₁ b₁ a₂ b₂).Adj :=
  inferInstanceAs
    (DecidableRel (twoSwitch (KddUnion 2 d) (0, .inl a₁) (0, .inr b₁) (1, .inl a₂) (1, .inr b₂)).Adj)

/-- Vertex type of `G_n = k H_d ∪ r K_{d,d}` with `m = n/(2d) = 2k + r`, `r ∈ {0,1}`. -/
abbrev GnV (d m : ℕ) : Type :=
  (Fin (m / 2) × (Fin 2 × (Fin d ⊕ Fin d))) ⊕ (Fin (m % 2) × (Fin d ⊕ Fin d))

/-- `G_n = k H_d ∪ r K_{d,d}` (Theorem D), `k = m / 2`, `r = m % 2`. -/
abbrev Gn (d m : ℕ) (a₁ b₁ a₂ b₂ : Fin d) : SimpleGraph (GnV d m) :=
  copies (m / 2) (Hd d a₁ b₁ a₂ b₂) ⊕g KddUnion (m % 2) d

instance (d m : ℕ) (a₁ b₁ a₂ b₂ : Fin d) : DecidableRel (Gn d m a₁ b₁ a₂ b₂).Adj :=
  inferInstanceAs (DecidableRel (copies (m / 2) (Hd d a₁ b₁ a₂ b₂) ⊕g KddUnion (m % 2) d).Adj)

/-- The triangular prism `K_3 □ K_2` (Mathlib's box product of complete graphs). -/
abbrev prism : SimpleGraph (Fin 3 × Fin 2) :=
  (⊤ : SimpleGraph (Fin 3)) □ (⊤ : SimpleGraph (Fin 2))

/-- `3 K_4`. -/
abbrev threeK4 : SimpleGraph (Fin 3 × Fin 4) :=
  copies 3 (⊤ : SimpleGraph (Fin 4))

/-- The competitor of the paragraph after Theorem A for `d ≥ 3`:
`(K_d □ K_2) ∪ (m - 1) K_{d,d}`. -/
abbrev prismUnion (d m : ℕ) : SimpleGraph ((Fin d × Fin 2) ⊕ (Fin (m - 1) × (Fin d ⊕ Fin d))) :=
  ((⊤ : SimpleGraph (Fin d)) □ (⊤ : SimpleGraph (Fin 2))) ⊕g KddUnion (m - 1) d

/-! ## §2. The question -/

/-- **Carenini's Question 1.3** for fixed `(n, d, γ)` (verbatim `Carenini.CareniniQuestion`):
every `d`-regular graph on `n` vertices has `i_γ` at most that of `(n / (2d)) K_{d,d}`. -/
def CareniniQuestion (n d : ℕ) (γ : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n → G.IsRegularOfDegree d →
      iGamma G d γ ≤ iGamma (KddUnion (n / (2 * d)) d) d γ

/-- The question restricted to bipartite graphs (Theorem B′: "even among bipartite graphs"). -/
def CareniniQuestionBip (n d : ℕ) (γ : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = n → G.IsRegularOfDegree d → G.IsBipartite →
      iGamma G d γ ≤ iGamma (KddUnion (n / (2 * d)) d) d γ

/-- `(n, d)` is admissible: `d ≥ 1`, `n ≥ 1` and `2d ∣ n`. -/
def Admissible (n d : ℕ) : Prop :=
  1 ≤ d ∧ 1 ≤ n ∧ 2 * d ∣ n

/-- `t* = dn/2 - 3d + 1` as an integer (`dn` is even whenever a `d`-regular graph on `n` vertices
exists; the statements below only use it in that situation). -/
def tStar (n d : ℕ) : ℤ :=
  ((d * n / 2 : ℕ) : ℤ) - 3 * d + 1

/-- `γ* = t*/(dn)`. -/
noncomputable def gammaStar (n d : ℕ) : ℝ :=
  (tStar n d : ℝ) / ((d : ℝ) * n)

/-! ## §3. Polynomials and the exponent `ρ(d, γ)` -/

/-- `P_d(z) = ∑_{a,b=0}^d C(d,a) C(d,b) z^{ab}`. -/
noncomputable def Pd (d : ℕ) : ℤ[X] :=
  ∑ a ∈ range (d + 1), ∑ b ∈ range (d + 1),
    Polynomial.C (((d.choose a) * (d.choose b) : ℕ) : ℤ) * X ^ (a * b)

/-- `W_{αβ}(z) = ∑_{i,j=0}^{d-1} C(d-1,i) C(d-1,j) z^{ij + αj + βi}` (used with `α, β ∈ {0,1}`). -/
noncomputable def Wpoly (d α β : ℕ) : ℤ[X] :=
  ∑ i ∈ range d, ∑ j ∈ range d,
    Polynomial.C ((((d - 1).choose i) * ((d - 1).choose j) : ℕ) : ℤ) *
      X ^ (i * j + α * j + β * i)

/-- `D(z) = W₀₀(z) W₁₁(z) - W₁₀(z)²`. -/
noncomputable def Dpoly (d : ℕ) : ℤ[X] :=
  Wpoly d 0 0 * Wpoly d 1 1 - Wpoly d 1 0 ^ 2

/-- `q ↦ (1/(2d)) log P_d(q) - γ d log q`. -/
noncomputable def rhoFun (d : ℕ) (γ q : ℝ) : ℝ :=
  1 / (2 * (d : ℝ)) * Real.log (evalR (Pd d) q) - γ * d * Real.log q

/-- `ρ(d, γ) = inf_{0 < q ≤ 1} ((1/(2d)) log P_d(q) - γ d log q)`. -/
noncomputable def rho (d : ℕ) (γ : ℝ) : ℝ :=
  ⨅ q : Set.Ioc (0 : ℝ) 1, rhoFun d γ q

/-! ## Tier 0: facts from §3 (Preliminaries) and §9 (Formal verification) -/

/-- §9: `i_γ = N_{≤⌊γdn⌋}` for `γ ≥ 0` (`Carenini.iGamma_eq_iCount_floor`). -/
def IGammaFloor : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (γ : ℝ), 0 ≤ γ →
      iGamma G d γ = iCount G ⌊γ * d * (Fintype.card V : ℝ)⌋₊

/-- §9: `i_γ` is invariant under graph isomorphism (`Carenini.iGamma_iso`, there for `γ ≥ 0`). -/
def IGammaIso : Prop :=
  ∀ (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj],
    Nonempty (G ≃g H) → ∀ (d : ℕ) (γ : ℝ), 0 ≤ γ → iGamma G d γ = iGamma H d γ

/-- §3: `P_{G ∪ F} = P_G P_F`, `P_{K_{d,d}} = P_d`, `P_{m K_{d,d}} = P_d^m`. -/
def PolyFacts : Prop :=
  (∀ (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (F : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel F.Adj],
      edgePoly (G ⊕g F) = edgePoly G * edgePoly F) ∧
  (∀ d : ℕ, edgePoly (Kdd d) = Pd d) ∧
  (∀ m d : ℕ, edgePoly (KddUnion m d) = Pd d ^ m) ∧
  (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ),
      (iCount G t : ℤ) = ∑ s ∈ range (t + 1), (edgePoly G).coeff s)

/-- §3: for admissible `(n, d)`, Question 1.3 (for all `γ ≥ 0`) is equivalent to the inequalities
`N_{≤t}(G) ≤ N_{≤t}(m K_{d,d})` for all integers `t ≥ 0`. -/
def IntegerForm : Prop :=
  ∀ n d : ℕ, Admissible n d →
    ((∀ γ : ℝ, 0 ≤ γ → CareniniQuestion n d γ) ↔
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        Fintype.card V = n → G.IsRegularOfDegree d →
          ∀ t : ℕ, iCount G t ≤ iCount (KddUnion (n / (2 * d)) d) t)

/-- §9, Table 4: the five negative results proved in v1.3.0 (`Carenini.not_careniniQuestion_*`). -/
def Neg_6_3 : Prop := ¬ CareniniQuestion 6 3 (1 / 18)

def Neg_2d : Prop := ∀ d : ℕ, 3 ≤ d → ¬ CareniniQuestion (2 * d) d (1 / (2 * (d : ℝ) ^ 2))

def Neg_8_2 : Prop := ¬ CareniniQuestion 8 2 (1 / 16)

def Neg_12_3_bip : Prop := ¬ CareniniQuestion 12 3 (1 / 36)

def Neg_12_3_top : Prop := ¬ CareniniQuestion 12 3 (5 / 18)

/-- §9, Table 4 and Remark 4: the counts `28 > 24`, `111 > 105`, `527 > 495`, `4002 > 3981`
(here `H_3` is `Hd 3 0 0 0 0` and `C_8` is Mathlib's `cycleGraph 8`). -/
def Table4Counts : Prop :=
  iCount prism 1 = 28 ∧ iCount (Kdd 3) 1 = 24 ∧
  iCount (cycleGraph 8) 1 = 111 ∧ iCount (KddUnion 2 2) 1 = 105 ∧
  iCount (Hd 3 0 0 0 0) 1 = 527 ∧ iCount (KddUnion 2 3) 1 = 495 ∧
  iCount threeK4 10 = 4002 ∧ iCount (KddUnion 2 3) 10 = 3981

/-- §1: `K_{d,d}` has `2^{d+1} - 1` independent sets. -/
def KddIndependentSets : Prop :=
  ∀ d : ℕ, iCount (Kdd d) 0 = 2 ^ (d + 1) - 1

/-! ## Tier 1: the numbered and named results -/

/-- **Lemma 1 (complement identity).** For a `d`-regular `G` with `n` vertices and `E` edges:
`∂(S) = d|S| - e_G(S)`, and for every integer `t`,
`N_{≤t}(G) = 2^n - #{S : ∂(S) ≤ E - t - 1}`. -/
def Lemma1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ),
    G.IsRegularOfDegree d →
      (∀ S : Finset V, boundary G S + edgesIn G S = d * #S) ∧
      ∀ t : ℤ, (NleZ G t : ℤ) = 2 ^ Fintype.card V -
        #((univ : Finset (Finset V)).filter
          (fun S => (boundary G S : ℤ) ≤ (#G.edgeFinset : ℤ) - t - 1))

/-- **Proposition 2.** For `d ≥ 2`, a `d`-regular `G` on `n` vertices and `t* = dn/2 - 3d + 1`:
`N_{≤t*}(G) = 2^n - 1 - n - C(n,2) - n C(d,2) + 2T(G) - Q(G)`. -/
def Proposition2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ),
    2 ≤ d → G.IsRegularOfDegree d →
      (NleZ G (tStar (Fintype.card V) d) : ℤ) =
        2 ^ Fintype.card V - 1 - Fintype.card V - (Fintype.card V).choose 2 -
          Fintype.card V * d.choose 2 + 2 * triangles G - Qcount G d

/-- **Lemma 3.** For a `d`-regular `G`: `Q = 0` if `d ≥ 5`; `Q ≤ (3/5) T` if `d = 4`;
`Q ≤ T/2` if `d = 3`; `Q = c₄(G)` if `d = 2`; and `2T - Q ≥ (7/5) T` if `d ≥ 3`. -/
def Lemma3 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ),
    G.IsRegularOfDegree d →
      (5 ≤ d → Qcount G d = 0) ∧
      (d = 4 → 5 * Qcount G d ≤ 3 * triangles G) ∧
      (d = 3 → 2 * Qcount G d ≤ triangles G) ∧
      (d = 2 → Qcount G d = c4 G) ∧
      (3 ≤ d → 7 * (triangles G : ℤ) ≤ 5 * (2 * (triangles G : ℤ) - Qcount G d))

/-- **Theorem A.** `d ≥ 2`, `n` a positive multiple of `2d`, `(n, d) ≠ (4, 2)`,
`m = n/(2d)`, `t* = dn/2 - 3d + 1`, `γ* = t*/(dn) = 1/2 - (3d-1)/(dn)`. Then `t* ≥ 1`, and
(a) if `d ≥ 3`, every `d`-regular `G` on `n` vertices has
`i_{γ*}(G) - i_{γ*}(m K_{d,d}) ≥ (7/5) T(G)`, with equality of the two counts iff `G` is
triangle-free (so `m K_{d,d}` minimises `i_{γ*}`, and every graph with a triangle has a larger
value); (b) if `d = 2`, every 2-regular `G ≇ m C₄ = m K_{2,2}` on `n` vertices has
`i_{γ*}(G) > i_{γ*}(m C₄)`. -/
def TheoremA : Prop :=
  ∀ n d : ℕ, 2 ≤ d → 0 < n → 2 * d ∣ n → (n, d) ≠ (4, 2) →
    1 ≤ tStar n d ∧
    gammaStar n d = 1 / 2 - (3 * (d : ℝ) - 1) / ((d : ℝ) * n) ∧
    (3 ≤ d →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        Fintype.card V = n → G.IsRegularOfDegree d →
          (7 / 5 : ℝ) * (triangles G : ℝ) ≤
              (iGamma G d (gammaStar n d) : ℝ) -
                iGamma (KddUnion (n / (2 * d)) d) d (gammaStar n d) ∧
            (iGamma G d (gammaStar n d) = iGamma (KddUnion (n / (2 * d)) d) d (gammaStar n d) ↔
              G.CliqueFree 3)) ∧
    (d = 2 →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        Fintype.card V = n → G.IsRegularOfDegree 2 → IsEmpty (G ≃g KddUnion (n / 4) 2) →
          iGamma (KddUnion (n / 4) 2) 2 (gammaStar n 2) < iGamma G 2 (gammaStar n 2))

/-- **Remark 4.** (i) For `n = 2d`, every triangle-free `d`-regular graph is `K_{d,d}`;
(ii) hence for `d ≥ 3` every `d`-regular graph on `2d` vertices other than `K_{d,d}` beats it at
`t* = d² - 3d + 1`; (iii) for `(n, d) = (12, 3)`: `t* = 10`, `γ* = 5/18`, `T(3K₄) = 12`,
`Q(3K₄) = 3`, and `N_{≤10}(3K₄) = 4002 = 3981 + 21`, `N_{≤10}(2K_{3,3}) = 3981`. -/
def Remark4 : Prop :=
  (∀ d : ℕ, 1 ≤ d →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = 2 * d → G.IsRegularOfDegree d → G.CliqueFree 3 →
        Nonempty (G ≃g Kdd d)) ∧
  (∀ d : ℕ, 3 ≤ d →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = 2 * d → G.IsRegularOfDegree d → IsEmpty (G ≃g Kdd d) →
        iCount (Kdd d) (d ^ 2 - 3 * d + 1) < iCount G (d ^ 2 - 3 * d + 1)) ∧
  tStar 12 3 = 10 ∧ gammaStar 12 3 = 5 / 18 ∧
  triangles threeK4 = 12 ∧ Qcount threeK4 3 = 3 ∧
  iCount threeK4 10 = 4002 ∧ iCount (KddUnion 2 3) 10 = 3981 ∧
  (iCount threeK4 10 : ℤ) - iCount (KddUnion 2 3) 10 = 21

/-- **Theorem B.** For `d ≥ 3` (and any labelling `x₁ ≠ x₂`, `y₁ ≠ y₂`): `S_d` is `d`-regular;
every set spanning at most one edge of `K_{d,d}` spans at most one edge of `S_d`;
`N_{≤1}(S_d) = N_{≤1}(K_{d,d}) + 4d - 8 = 2^{d+1} + d² + 4d - 9`; and for `n = 2d` and every
`γ ∈ [1/(2d²), 1/d²)`, `K_{d,d}` does not maximise `i_γ`. -/
def TheoremB : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ a₁ a₂ b₁ b₂ : Fin d, a₁ ≠ a₂ → b₁ ≠ b₂ →
    (Sd d a₁ a₂ b₁ b₂).IsRegularOfDegree d ∧
    (∀ A : Finset (Fin d ⊕ Fin d), edgesIn (Kdd d) A ≤ 1 → edgesIn (Sd d a₁ a₂ b₁ b₂) A ≤ 1) ∧
    (iCount (Sd d a₁ a₂ b₁ b₂) 1 : ℤ) = iCount (Kdd d) 1 + (4 * d - 8) ∧
    (iCount (Sd d a₁ a₂ b₁ b₂) 1 : ℤ) = 2 ^ (d + 1) + (d : ℤ) ^ 2 + 4 * d - 9 ∧
    ∀ γ : ℝ, 1 / (2 * (d : ℝ) ^ 2) ≤ γ → γ < 1 / (d : ℝ) ^ 2 → ¬ CareniniQuestion (2 * d) d γ

/-- **Corollary 5.** `d ≥ 3`, `m ≥ 2`, `I = 2^{d+1} - 1`:
`N_{≤1}(S_d ∪ (m-1)K_{d,d}) - N_{≤1}(m K_{d,d}) = I^{m-2} [(4d-8) I - (m-1) d² (2^{d-1} - 2)]`;
for `n = 2dm` and `γ ∈ [1/(dn), 2/(dn))`, `S_d ∪ (m-1)K_{d,d}` beats `m K_{d,d}` iff
`(4d-8) I > (m-1) d² (2^{d-1} - 2)`; and this criterion holds exactly for `d = 3, 2 ≤ m ≤ 4`,
`d ∈ {4,5}, 2 ≤ m ≤ 3`, `6 ≤ d ≤ 13, m = 2` (in particular never for `d ≥ 14`).
Also `i_0(S_d) = 3·2^{d-1} + 1` (used in the proof). -/
def Corollary5 : Prop :=
  (∀ d m : ℕ, 3 ≤ d → 2 ≤ m → ∀ a₁ a₂ b₁ b₂ : Fin d, a₁ ≠ a₂ → b₁ ≠ b₂ →
    (iCount (Sd d a₁ a₂ b₁ b₂ ⊕g KddUnion (m - 1) d) 1 : ℤ) - iCount (KddUnion m d) 1 =
        (2 ^ (d + 1) - 1) ^ (m - 2) *
          ((4 * (d : ℤ) - 8) * (2 ^ (d + 1) - 1) -
            ((m : ℤ) - 1) * (d : ℤ) ^ 2 * (2 ^ (d - 1) - 2)) ∧
    (∀ γ : ℝ, 1 / ((d : ℝ) * (2 * d * m)) ≤ γ → γ < 2 / ((d : ℝ) * (2 * d * m)) →
      (iGamma (KddUnion m d) d γ < iGamma (Sd d a₁ a₂ b₁ b₂ ⊕g KddUnion (m - 1) d) d γ ↔
        ((m : ℤ) - 1) * (d : ℤ) ^ 2 * (2 ^ (d - 1) - 2) <
          (4 * (d : ℤ) - 8) * (2 ^ (d + 1) - 1)))) ∧
  (∀ d m : ℕ, 3 ≤ d → 2 ≤ m →
    (((m : ℤ) - 1) * (d : ℤ) ^ 2 * (2 ^ (d - 1) - 2) < (4 * (d : ℤ) - 8) * (2 ^ (d + 1) - 1) ↔
      (d = 3 ∧ m ≤ 4) ∨ ((d = 4 ∨ d = 5) ∧ m ≤ 3) ∨ (6 ≤ d ∧ d ≤ 13 ∧ m = 2))) ∧
  (∀ d : ℕ, 3 ≤ d → ∀ a₁ a₂ b₁ b₂ : Fin d, a₁ ≠ a₂ → b₁ ≠ b₂ →
    iCount (Sd d a₁ a₂ b₁ b₂) 0 = 3 * 2 ^ (d - 1) + 1)

/-- §4.2 (text before Lemma 6): `W₁₀ = W₀₁`. -/
def WSymm : Prop :=
  ∀ d : ℕ, Wpoly d 1 0 = Wpoly d 0 1

/-- **Lemma 6.** For `d ≥ 2` and `H_d` as in Theorem B′ (any choice of `u_k`, `w_k`):
`P_{2K}(z) - P_{H_d}(z) = 2(z - 1) D(z)`, and for every graph `F` (possibly with no vertices) and
every integer `t ≥ 0`, `N_{≤t}(H_d ∪ F) - N_{≤t}(2K ∪ F) = 2 [z^t](D(z) P_F(z))`. -/
def Lemma6 : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ a₁ b₁ a₂ b₂ : Fin d,
    edgePoly (KddUnion 2 d) - edgePoly (Hd d a₁ b₁ a₂ b₂) = 2 * (X - 1) * Dpoly d ∧
    ∀ (W : Type) [Fintype W] [DecidableEq W] (F : SimpleGraph W) [DecidableRel F.Adj] (t : ℕ),
      (iCount (Hd d a₁ b₁ a₂ b₂ ⊕g F) t : ℤ) - iCount (KddUnion 2 d ⊕g F) t =
        2 * (Dpoly d * edgePoly F).coeff t

/-- **Lemma 7.** For `d ≥ 2` and `q > 0`: `D(q) > 0` if `q > 1` and `D(q) < 0` if `q < 1`. -/
def Lemma7 : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ q : ℝ, 0 < q →
    (1 < q → 0 < evalR (Dpoly d) q) ∧ (q < 1 → evalR (Dpoly d) q < 0)

/-- **Theorem B′.** For `d ≥ 2` and any choice of `u_k ∈ X_k`, `w_k ∈ Y_k`: `H_d` is `d`-regular,
bipartite and connected; `N_{≤1}(H_d) - N_{≤1}(2K_{d,d}) = 2(d-1)(2^d + d - 3) > 0`;
`i_0(H_d) - i_0(2K_{d,d}) = -2(2^{d-1} - 1)²`; and for `n = 4d` and every
`γ ∈ [1/(4d²), 1/(2d²))`, `2K_{d,d}` does not maximise `i_γ` even among bipartite `d`-regular
graphs on `n` vertices. -/
def TheoremBprime : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ a₁ b₁ a₂ b₂ : Fin d,
    (Hd d a₁ b₁ a₂ b₂).IsRegularOfDegree d ∧ (Hd d a₁ b₁ a₂ b₂).IsBipartite ∧
    (Hd d a₁ b₁ a₂ b₂).Connected ∧
    (iCount (Hd d a₁ b₁ a₂ b₂) 1 : ℤ) - iCount (KddUnion 2 d) 1 =
      2 * ((d : ℤ) - 1) * (2 ^ d + (d : ℤ) - 3) ∧
    0 < 2 * ((d : ℤ) - 1) * (2 ^ d + (d : ℤ) - 3) ∧
    (iCount (Hd d a₁ b₁ a₂ b₂) 0 : ℤ) - iCount (KddUnion 2 d) 0 = -2 * (2 ^ (d - 1) - 1) ^ 2 ∧
    ∀ γ : ℝ, 1 / (4 * (d : ℝ) ^ 2) ≤ γ → γ < 1 / (2 * (d : ℝ) ^ 2) →
      ¬ CareniniQuestionBip (4 * d) d γ

/-- **Lemma 8 (lower bound in Cramér's theorem)**, stated with Mathlib's probability theory.
`p : PMF ℕ` is the law of `ξ`, supported on `{0, …, M}`, with `P(ξ = 0) > 0`, `P(ξ = M) > 0`;
`E ξ = ∫ i dp` and `Λ(λ) = log ∫ e^{λ i} dp`. For each `m`, the claim is about **every** family
`ξ₁, …, ξ_m` of independent random variables with law `p` on any probability space (the law of
`Σ_m` depends only on `p`):
(a) if `E ξ < x < M` then `liminf_m (1/m) log P(Σ_m > mx) ≥ inf_{λ ≥ 0} (Λ(λ) - λx)`;
(b) if `0 < x < E ξ` then `liminf_m (1/m) log P(Σ_m < mx) ≥ inf_{λ ≤ 0} (Λ(λ) - λx)`. -/
def Lemma8 : Prop :=
  ∀ (M : ℕ) (p : PMF ℕ), (∀ i, M < i → p i = 0) → p 0 ≠ 0 → p M ≠ 0 →
    (∀ x : ℝ, (∫ i, (i : ℝ) ∂p.toMeasure) < x → x < M → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop,
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure P] (ξ : Fin m → Ω → ℕ),
          ProbabilityTheory.iIndepFun ξ P → (∀ i, ProbabilityTheory.HasLaw (ξ i) p.toMeasure P) →
            Real.exp (m * ((⨅ l : Set.Ici (0 : ℝ),
                (Real.log (∫ i, Real.exp (l * i) ∂p.toMeasure) - l * x)) - ε)) ≤
              (P {ω | (m : ℝ) * x < ∑ i, (ξ i ω : ℝ)}).toReal) ∧
    (∀ x : ℝ, 0 < x → x < (∫ i, (i : ℝ) ∂p.toMeasure) → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop,
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure P] (ξ : Fin m → Ω → ℕ),
          ProbabilityTheory.iIndepFun ξ P → (∀ i, ProbabilityTheory.HasLaw (ξ i) p.toMeasure P) →
            Real.exp (m * ((⨅ l : Set.Iic (0 : ℝ),
                (Real.log (∫ i, Real.exp (l * i) ∂p.toMeasure) - l * x)) - ε)) ≤
              (P {ω | ∑ i, (ξ i ω : ℝ) < m * x}).toReal)

/-- The infima in Lemma 8 are over families bounded below (so `⨅` is the true infimum). -/
def Lemma8_bddBelow : Prop :=
  ∀ (M : ℕ) (p : PMF ℕ), (∀ i, M < i → p i = 0) → p 0 ≠ 0 → p M ≠ 0 → ∀ x : ℝ, 0 ≤ x → x ≤ M →
    BddBelow (Set.range fun l : Set.Ici (0 : ℝ) =>
      Real.log (∫ i, Real.exp (l * i) ∂p.toMeasure) - l * x) ∧
    BddBelow (Set.range fun l : Set.Iic (0 : ℝ) =>
      Real.log (∫ i, Real.exp (l * i) ∂p.toMeasure) - l * x)

/-- **Proposition C.** `d ≥ 2`, `γ ≥ 0`: every `d`-regular `G` on `n ≥ 1` vertices satisfies
`(1/n) log i_γ(G) ≤ ρ(d, γ)`, and `(1/n) log i_γ(m K_{d,d}) → ρ(d, γ)` as `n = 2dm → ∞`. -/
def PropositionC : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ γ : ℝ, 0 ≤ γ →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      0 < Fintype.card V → G.IsRegularOfDegree d →
        1 / (Fintype.card V : ℝ) * Real.log (iGamma G d γ) ≤ rho d γ) ∧
    Tendsto (fun m : ℕ => 1 / ((2 * d * m : ℕ) : ℝ) * Real.log (iGamma (KddUnion m d) d γ))
      atTop (𝓝 (rho d γ))

/-- The family defining `ρ(d, γ)` is bounded below (so `rho` is the true infimum). -/
def Rho_bddBelow : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ γ : ℝ, 0 ≤ γ →
    BddBelow (Set.range fun q : Set.Ioc (0 : ℝ) 1 => rhoFun d γ q)

/-- **Theorem D.** `d ≥ 2`, `1/8 < γ < 1/2`; `G_n = k H_d ∪ r K_{d,d}` with `n/(2d) = 2k + r`,
`r ∈ {0,1}`, is a bipartite `d`-regular graph on `n` vertices, and
`i_γ(G_n) > i_γ(m K_{d,d})` (`m = n/(2d)`) for all sufficiently large `n` divisible by `2d`. -/
def TheoremD : Prop :=
  (∀ d m : ℕ, 2 ≤ d → ∀ a₁ b₁ a₂ b₂ : Fin d,
    Fintype.card (GnV d m) = 2 * d * m ∧ (Gn d m a₁ b₁ a₂ b₂).IsRegularOfDegree d ∧
      (Gn d m a₁ b₁ a₂ b₂).IsBipartite) ∧
  (∀ d : ℕ, 2 ≤ d → ∀ γ : ℝ, 1 / 8 < γ → γ < 1 / 2 → ∀ a₁ b₁ a₂ b₂ : Fin d,
    ∃ M₀ : ℕ, ∀ m ≥ M₀, iGamma (KddUnion m d) d γ < iGamma (Gn d m a₁ b₁ a₂ b₂) d γ)

/-! ## Tier C: cited theorems the proofs rely on (not in Mathlib) -/

/-- Sah–Sawhney–Stoner–Zhao, Corollary 1.15 (antiferromagnetic 2-spin models are
biclique-maximising), in the form used by Carenini's Proposition 2.1 with fugacity `1`:
for a `d`-regular `G` on `n` vertices and `0 < q ≤ 1`, `P_G(q) ≤ P_d(q)^{n/(2d)}`. -/
def SSSZBound : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree d → ∀ q : ℝ, 0 < q → q ≤ 1 →
        evalR (edgePoly G) q ≤ evalR (Pd d) q ^ ((Fintype.card V : ℝ) / (2 * d))

/-- Carenini, Proposition 2.1 with `λ = 1`: `i_γ(G) ≤ e^{γtn} P_d(e^{-t/d})^{n/(2d)}` for every
`t ≥ 0`. -/
def CareniniProp21 : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree d → ∀ γ : ℝ, 0 ≤ γ → ∀ t : ℝ, 0 ≤ t →
        (iGamma G d γ : ℝ) ≤ Real.exp (γ * t * Fintype.card V) *
          evalR (Pd d) (Real.exp (-t / d)) ^ ((Fintype.card V : ℝ) / (2 * d))

/-- Kahn (bipartite) and Zhao (all `d`-regular graphs): `i_0(G) ≤ (2^{d+1} - 1)^{n/(2d)}`. -/
def KahnZhao : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.IsRegularOfDegree d →
        (iCount G 0 : ℝ) ≤ ((2 : ℝ) ^ (d + 1) - 1) ^ ((Fintype.card V : ℝ) / (2 * d))

/-! ## Tier 2: claims in the abstract, introduction, readings table and remarks -/

/-- §1: for `γ ≥ 1/2` the question holds trivially. -/
def QuestionTrueHalf : Prop :=
  ∀ n d : ℕ, Admissible n d → ∀ γ : ℝ, 1 / 2 ≤ γ → CareniniQuestion n d γ

/-- §1, readings R4/R6: for `γ = 0` the answer is yes (the Kahn–Zhao theorem). -/
def QuestionTrueZero : Prop :=
  ∀ n d : ℕ, Admissible n d → CareniniQuestion n d 0

/-- Abstract and §1: for `d = 1` and for `(n, d) = (4, 2)` only one `d`-regular graph exists
(up to isomorphism), namely `(n/(2d)) K_{d,d}`. -/
def TrivialCasesUnique : Prop :=
  (∀ n : ℕ, 0 < n → 2 ∣ n →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → G.IsRegularOfDegree 1 → Nonempty (G ≃g KddUnion (n / 2) 1)) ∧
  (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = 4 → G.IsRegularOfDegree 2 → Nonempty (G ≃g KddUnion 1 2))

/-- Reading R2: in the trivial cases the question holds for every `γ`. -/
def TrivialCasesTrue : Prop :=
  ∀ n d : ℕ, Admissible n d → (d = 1 ∨ (n = 4 ∧ d = 2)) → ∀ γ : ℝ, CareniniQuestion n d γ

/-- §1 (paragraph after Theorem A): the competitors exist. For `d ≥ 3`,
`(K_d □ K_2) ∪ (m-1) K_{d,d}` has `2dm` vertices, is `d`-regular and contains a triangle; for
`d = 2` and `n ≥ 8` (`4 ∣ n`), `C_n` is 2-regular and not isomorphic to `(n/4) C₄`. Also
`C₄ = K_{2,2}`. -/
def CompetitorFacts : Prop :=
  (∀ d m : ℕ, 3 ≤ d → 1 ≤ m →
    Fintype.card ((Fin d × Fin 2) ⊕ (Fin (m - 1) × (Fin d ⊕ Fin d))) = 2 * d * m ∧
    (prismUnion d m).IsRegularOfDegree d ∧ ¬ (prismUnion d m).CliqueFree 3) ∧
  (∀ n : ℕ, 8 ≤ n → 4 ∣ n →
    (cycleGraph n).IsRegularOfDegree 2 ∧ IsEmpty (cycleGraph n ≃g KddUnion (n / 4) 2)) ∧
  Nonempty (cycleGraph 4 ≃g Kdd 2)

/-- Abstract, §1 (italic claim) and reading R2: the answer is negative for every admissible
`(n, d)` except `d = 1` and `(n, d) = (4, 2)`, at `γ = γ* ∈ (0, 1/2)`. -/
def NegativeEveryAdmissible : Prop :=
  ∀ n d : ℕ, Admissible n d → 2 ≤ d → (n, d) ≠ (4, 2) →
    0 < gammaStar n d ∧ gammaStar n d < 1 / 2 ∧ ¬ CareniniQuestion n d (gammaStar n d)

/-- Carenini's Question 1.3 as one statement (reading R1): for all `d ≥ 1`, all `n` divisible by
`2d` and all `γ ≥ 0`, the inequality holds. (Added in version 2, review item M1.) -/
def Question13 : Prop :=
  ∀ n d : ℕ, 1 ≤ d → 2 * d ∣ n → ∀ γ : ℝ, 0 ≤ γ → CareniniQuestion n d γ

/-- Title and abstract: the answer to Question 1.3 is negative. (Added in version 2.) -/
def AnswerNegative : Prop :=
  ¬ Question13

/-- §1, "Scope": `γ* > 1/8` unless `(n, d) = (6, 3)`, and `γ* → 1/2` as `n → ∞` (fixed `d`);
for `(n, d) = (6, 3)`, `t* = 1` and `γ* = 1/18` (the last conjunct was added in version 2,
review item M2). -/
def GammaStarScope : Prop :=
  (∀ n d : ℕ, Admissible n d → 2 ≤ d → (n, d) ≠ (4, 2) → (n, d) ≠ (6, 3) →
    1 / 8 < gammaStar n d) ∧
  (∀ d : ℕ, 1 ≤ d → Tendsto (fun m : ℕ => gammaStar (2 * d * m) d) atTop (𝓝 (1 / 2))) ∧
  tStar 6 3 = 1 ∧ gammaStar 6 3 = 1 / 18

/-- §1, "Scope": every counterexample of the paper with `γ ≤ 1/8` has `γ d < 1`. (Added in
version 2.) The counterexamples with `γ ≤ 1/8` are: Theorem B (`γ < 1/d²`; this includes the row
`(2d, d, 1/(2d²))` of Table 4), Theorem B′ (`γ < 1/(2d²)`) and Corollary 5
(`γ < 2/(dn) = 1/(d²m)`), all covered by the first conjunct; and examples with `d ≤ 5`, covered by
the second conjunct: Theorem A at `(n, d) = (6, 3)` (for every other pair with `d ≥ 2`,
`(n, d) ≠ (4, 2)`, `γ* > 1/8` by `GammaStarScope`), the other rows of Table 4, Remark 12
(`d = 2, 3`) and Table 2 (`d = 3, 4, 5`). -/
def LowGammaExamples : Prop :=
  (∀ d : ℕ, 1 ≤ d → ∀ γ : ℝ, γ < 1 / (d : ℝ) ^ 2 → γ * d < 1) ∧
  (∀ d : ℕ, d ≤ 5 → ∀ γ : ℝ, γ ≤ 1 / 8 → γ * d < 1)

/-- The prism is Theorem B's `S_3`, and Theorem B′'s `H_2` is the cycle `C₈`. -/
def S3PrismH2Cycle : Prop :=
  (∀ a₁ a₂ b₁ b₂ : Fin 3, a₁ ≠ a₂ → b₁ ≠ b₂ → Nonempty (Sd 3 a₁ a₂ b₁ b₂ ≃g prism)) ∧
  (∀ a₁ b₁ a₂ b₂ : Fin 2, Nonempty (Hd 2 a₁ b₁ a₂ b₂ ≃g cycleGraph 8))

/-- §1 ("as Carenini notes"): Seth's density condition `e_G(J)/C(|J|,2) ≤ d/(kn)` (written
multiplicatively) implies `e_G(J) ≤ dn/(2k)`. -/
def SethDensity : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d k : ℕ),
    0 < k → 0 < Fintype.card V → ∀ J : Finset V,
      (edgesIn G J : ℝ) ≤ (d : ℝ) / (k * Fintype.card V) * ((#J).choose 2 : ℕ) →
        (edgesIn G J : ℝ) ≤ (d : ℝ) * Fintype.card V / (2 * k)

/-- §10, open question 4: by Proposition 2, at `γ = γ*` the maximisers of `i_{γ*}` among
`d`-regular graphs on `n` vertices are the maximisers of `2T(G) - Q(G)` (comparison form). -/
def MaximisersAtGammaStar : Prop :=
  ∀ n d : ℕ, 2 ≤ d →
    ∀ (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj],
      Fintype.card V = n → Fintype.card W = n → G.IsRegularOfDegree d → H.IsRegularOfDegree d →
        (iGamma G d (gammaStar n d) ≤ iGamma H d (gammaStar n d) ↔
          2 * (triangles G : ℤ) - Qcount G d ≤ 2 * (triangles H : ℤ) - Qcount H d)

/-- Table 1: `N_{≤t}` of `K_{3,3}` and of the prism for `t = 0, …, 9`. -/
def Table1 : Prop :=
  (List.range 10).map (fun t => iCount (Kdd 3) t) = [15, 24, 42, 48, 57, 57, 63, 63, 63, 64] ∧
  (List.range 10).map (fun t => iCount prism t) = [13, 28, 40, 48, 57, 57, 63, 63, 63, 64]

/-- §1: the only cubic graphs on six vertices are `K_{3,3}` and the prism. -/
def CubicSix : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Fintype.card V = 6 → G.IsRegularOfDegree 3 →
      Nonempty (G ≃g Kdd 3) ∨ Nonempty (G ≃g prism)

/-- §1: at `(n, d) = (6, 3)`, `K_{3,3}` fails to be a maximiser exactly for `γ ∈ [1/18, 1/9)`. -/
def ExactFailureSix : Prop :=
  ∀ γ : ℝ, 0 ≤ γ → (¬ CareniniQuestion 6 3 γ ↔ 1 / 18 ≤ γ ∧ γ < 1 / 9)

/-- §1, abstract, reading R1: `(6, 3, 1/18)` is the smallest counterexample (smallest `n`, then
smallest `γ` for that `n`). -/
def SmallestCounterexample : Prop :=
  ¬ CareniniQuestion 6 3 (1 / 18) ∧
  (∀ n d : ℕ, Admissible n d → n < 6 → ∀ γ : ℝ, 0 ≤ γ → CareniniQuestion n d γ) ∧
  (∀ d : ℕ, Admissible 6 d → ∀ γ : ℝ, 0 ≤ γ → γ < 1 / 18 → CareniniQuestion 6 d γ)

/-- **Remark 9**: `ρ(d, γ) = inf_{t ≥ 0} (γ t + (1/(2d)) log B_d(t))` with
`B_d(t) = P_d(e^{-t/d})`. -/
def Remark9 : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ γ : ℝ, 0 ≤ γ →
    rho d γ = ⨅ t : Set.Ici (0 : ℝ),
      (γ * t + 1 / (2 * (d : ℝ)) * Real.log (evalR (Pd d) (Real.exp (-t / d))))

/-- **Remark 10**, first part: for `γ > 1/8`, `i_γ(m K_{d,d}) = (1 - o(1)) 2^n`;
`i_γ(G_n)/i_γ(m K_{d,d}) - 1 ≤ U(m K_{d,d})/i_γ(m K_{d,d})`, which tends to `0` exponentially fast. -/
def Remark10a : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ γ : ℝ, 1 / 8 < γ →
    Tendsto (fun m : ℕ => (iGamma (KddUnion m d) d γ : ℝ) / 2 ^ (2 * d * m)) atTop (𝓝 1) ∧
    (∀ a₁ b₁ a₂ b₂ : Fin d, ∀ m : ℕ,
      (iGamma (Gn d m a₁ b₁ a₂ b₂) d γ : ℝ) / iGamma (KddUnion m d) d γ - 1 ≤
        ((2 : ℝ) ^ (2 * d * m) - iGamma (KddUnion m d) d γ) / iGamma (KddUnion m d) d γ) ∧
    ∃ C c : ℝ, 0 < c ∧ c < 1 ∧ ∀ m : ℕ,
      ((2 : ℝ) ^ (2 * d * m) - iGamma (KddUnion m d) d γ) / iGamma (KddUnion m d) d γ ≤ C * c ^ m

/-- **Remark 10**, numerical example: for `d = 2`, `γ = 1/4`, `n = 400` (`m = 100`) the relative
difference `i_γ(G_n)/i_γ(m K_{2,2}) - 1` is "about `1.3·10^{-17}`" (read: in
`[1.25·10^{-17}, 1.35·10^{-17})`). -/
def Remark10b : Prop :=
  (125 / 10 ^ 19 : ℝ) ≤
      (iGamma (Gn 2 100 0 0 0 0) 2 (1 / 4) : ℝ) / iGamma (KddUnion 100 2) 2 (1 / 4) - 1 ∧
    (iGamma (Gn 2 100 0 0 0 0) 2 (1 / 4) : ℝ) / iGamma (KddUnion 100 2) 2 (1 / 4) - 1 <
      135 / 10 ^ 19

/-- `φ(q) = log P_d(q) - x log q` with `x = 2γd²` (proof of Theorem D). -/
noncomputable def phiFun (d : ℕ) (γ q : ℝ) : ℝ :=
  Real.log (evalR (Pd d) q) - 2 * γ * (d : ℝ) ^ 2 * Real.log q

/-- `q*` is a minimiser of `φ` over `[1, ∞)`. -/
def IsQStar (d : ℕ) (γ q : ℝ) : Prop :=
  1 ≤ q ∧ ∀ q' : ℝ, 1 ≤ q' → phiFun d γ q ≤ phiFun d γ q'

/-- The base `P_d(q)² / P_{H_d}(q)` of Theorem D (canonical `H_d`). -/
noncomputable def baseRatio (d : ℕ) (a₁ b₁ a₂ b₂ : Fin d) (q : ℝ) : ℝ :=
  evalR (Pd d) q ^ 2 / evalR (edgePoly (Hd d a₁ b₁ a₂ b₂)) q

/-- **Remark 10**, the base (with the existence of `q* > 1` from the proof of Theorem D): it tends
to `1` as `γ ↓ 1/8`; for `d = 2` it is "about `1.0006`" at
`γ = 1/4` and "about `1.0001`" at `γ = 0.49` (read: `[1.00055, 1.00065)` and
`[1.00005, 1.00015)`). -/
def Remark10c : Prop :=
  (∀ d : ℕ, 2 ≤ d → ∀ γ : ℝ, 1 / 8 < γ → γ < 1 / 2 → ∃ q : ℝ, 1 < q ∧ IsQStar d γ q) ∧
  (∀ d : ℕ, 2 ≤ d → ∀ a₁ b₁ a₂ b₂ : Fin d, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ γ q : ℝ, 1 / 8 < γ → γ < 1 / 8 + δ → IsQStar d γ q →
      |baseRatio d a₁ b₁ a₂ b₂ q - 1| < ε) ∧
  (∀ q : ℝ, IsQStar 2 (1 / 4) q →
    (100055 / 100000 : ℝ) ≤ baseRatio 2 0 0 0 0 q ∧ baseRatio 2 0 0 0 0 q < 100065 / 100000) ∧
  (∀ q : ℝ, IsQStar 2 (49 / 100) q →
    (100005 / 100000 : ℝ) ≤ baseRatio 2 0 0 0 0 q ∧ baseRatio 2 0 0 0 0 q < 100015 / 100000)

/-- **Remark 10**, the mean and variance: for `A` uniform, `e_G(A)` has mean `dn/8` and variance
`dn(2d+1)/32` (as exact sums over all `2^n` sets). (Version 2: the normal approximation at
`γ = 1/8`, the second conjunct of version 1, is deleted.) -/
def Remark10d : Prop :=
  ∀ d : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsRegularOfDegree d →
      (∑ A : Finset V, (edgesIn G A : ℝ)) =
          2 ^ Fintype.card V * ((d : ℝ) * Fintype.card V / 8) ∧
        (∑ A : Finset V, ((edgesIn G A : ℝ) - (d : ℝ) * Fintype.card V / 8) ^ 2) =
          2 ^ Fintype.card V * ((d : ℝ) * Fintype.card V * (2 * d + 1) / 32)

/-- Reading R6 (ratio form) holds for `γ = 0` and for `γ > 1/8`:
`max_G i_γ(G) ≤ (1 + o(1)) i_γ(m K_{d,d})`. (Version 2: the case `γ = 1/8` is deleted.) -/
def ReadingR6 : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ γ : ℝ, (γ = 0 ∨ 1 / 8 < γ) → ∀ ε : ℝ, 0 < ε → ∃ M₀ : ℕ, ∀ m ≥ M₀,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = 2 * d * m → G.IsRegularOfDegree d →
        (iGamma G d γ : ℝ) ≤ (1 + ε) * iGamma (KddUnion m d) d γ

/-- **Remark 11**: for `0 < γ < 1/8`, `G_n` loses to `m K_{d,d}` for all large `n`. -/
def Remark11 : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ γ : ℝ, 0 < γ → γ < 1 / 8 → ∀ a₁ b₁ a₂ b₂ : Fin d,
    ∃ M₀ : ℕ, ∀ m ≥ M₀, iGamma (Gn d m a₁ b₁ a₂ b₂) d γ < iGamma (KddUnion m d) d γ

open Classical in
/-- **Remark 12**: at `γ = 1/10`, `G_n` beats `m K_{d,d}` for 92 of the 119 values
`n ∈ {8, 12, …, 480}` when `d = 2` (largest `n = 400`), and for 56 of the 119 values
`n ∈ {12, 18, …, 720}` when `d = 3` (largest `n = 360`); here `n = 2dm`, `2 ≤ m ≤ 120`. -/
def Remark12 : Prop :=
  #((Icc 2 120).filter fun m =>
      iGamma (KddUnion m 2) 2 (1 / 10) < iGamma (Gn 2 m 0 0 0 0) 2 (1 / 10)) = 92 ∧
  iGamma (KddUnion 100 2) 2 (1 / 10) < iGamma (Gn 2 100 0 0 0 0) 2 (1 / 10) ∧
  (∀ m ∈ Icc 101 120, iGamma (Gn 2 m 0 0 0 0) 2 (1 / 10) ≤ iGamma (KddUnion m 2) 2 (1 / 10)) ∧
  #((Icc 2 120).filter fun m =>
      iGamma (KddUnion m 3) 3 (1 / 10) < iGamma (Gn 3 m 0 0 0 0) 3 (1 / 10)) = 56 ∧
  iGamma (KddUnion 60 3) 3 (1 / 10) < iGamma (Gn 3 60 0 0 0 0) 3 (1 / 10) ∧
  (∀ m ∈ Icc 61 120, iGamma (Gn 3 m 0 0 0 0) 3 (1 / 10) ≤ iGamma (KddUnion m 3) 3 (1 / 10))

/-! ## Tier 3: computational claims of §8 -/

/-- §8: every `d`-regular graph on `2d` vertices is connected. -/
def RegularOn2dConnected : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = 2 * d → G.IsRegularOfDegree d → G.Connected

/-- §8 (parenthetical after Table 2): for `d ≥ 3`, all `d`-regular graphs on `n` vertices have the
same `N_{≤t}` when `t ≥ dn/2 - 2d`. -/
def HighThresholdTie : Prop :=
  ∀ d n : ℕ, 3 ≤ d → ∀ t : ℤ, ((d * n / 2 : ℕ) : ℤ) - 2 * d ≤ t →
    ∀ (V W : Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj],
      Fintype.card V = n → Fintype.card W = n → G.IsRegularOfDegree d → H.IsRegularOfDegree d →
        NleZ G t = NleZ H t

/-- One 2-switch step: replace the edges `u₁w₁`, `u₂w₂` by the non-edges `u₁w₂`, `u₂w₁`
(this covers both variants "`ac, bd`" and "`ad, bc`" of §8 by relabelling). -/
def TwoSwitchStep {V : Type*} (G G' : SimpleGraph V) : Prop :=
  ∃ u₁ w₁ u₂ w₂ : V, G.Adj u₁ w₁ ∧ G.Adj u₂ w₂ ∧ u₁ ≠ w₂ ∧ u₂ ≠ w₁ ∧
    ¬ G.Adj u₁ w₂ ∧ ¬ G.Adj u₂ w₁ ∧ G' = twoSwitch G u₁ w₁ u₂ w₂

/-- Cited in §8 (Hakimi; Fulkerson–Hoffman–McAndrew): two simple graphs on the same vertex set
with the same degree at every vertex are connected by a sequence of 2-switches. Only needed for
the class counts of Table 2 (Tier 3). -/
def TwoSwitchConnected : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj], (∀ v, G.degree v = H.degree v) → Relation.ReflTransGen TwoSwitchStep G H

section Table2

open Classical

/-- There are exactly `k` isomorphism classes of `d`-regular graphs on `Fin n`: a list of `k`
pairwise non-isomorphic `d`-regular graphs such that every `d`-regular graph is isomorphic to one
of them. -/
def HasClassCount (n d k : ℕ) : Prop :=
  ∃ R : Fin k → SimpleGraph (Fin n),
    (∀ i, (R i).IsRegularOfDegree d) ∧
    (∀ i j, Nonempty (R i ≃g R j) → i = j) ∧
    ∀ G : SimpleGraph (Fin n), G.IsRegularOfDegree d → ∃ i, Nonempty (G ≃g R i)

/-- `K_{d,d}` is not a maximiser of `N_{≤t}` among `d`-regular graphs on `2d` vertices. -/
def FailsAt (d t : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin (2 * d)), G.IsRegularOfDegree d ∧ iCount (Kdd d) t < iCount G t

/-- The maximum of `N_{≤t}` over `d`-regular graphs on `2d` vertices is `v`. -/
def MaxIs (d t v : ℕ) : Prop :=
  (∃ G : SimpleGraph (Fin (2 * d)), G.IsRegularOfDegree d ∧ iCount G t = v) ∧
  ∀ G : SimpleGraph (Fin (2 * d)), G.IsRegularOfDegree d → iCount G t ≤ v

/-- `K_{d,d}` is the unique maximiser (up to isomorphism) of `N_{≤t}`. -/
def UniqueMaxAt (d t : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin (2 * d)), G.IsRegularOfDegree d → IsEmpty (G ≃g Kdd d) →
    iCount G t < iCount (Kdd d) t

/-- `K_{d,d}` is a maximiser of `N_{≤t}` and ties with some non-isomorphic graph. -/
def TieMaxAt (d t : ℕ) : Prop :=
  (∀ G : SimpleGraph (Fin (2 * d)), G.IsRegularOfDegree d → iCount G t ≤ iCount (Kdd d) t) ∧
  ∃ G : SimpleGraph (Fin (2 * d)), G.IsRegularOfDegree d ∧ IsEmpty (G ≃g Kdd d) ∧
    iCount G t = iCount (Kdd d) t

/-- The data of Table 2 for one `d`: failure thresholds with `(t, max, N_{≤t}(K_{d,d}))`, and the
thresholds where `K_{d,d}` is the unique maximiser; at all other `t ≤ d²` it ties. -/
def Table2Row (d k : ℕ) (fails : List (ℕ × ℕ × ℕ)) (uniq : List ℕ) : Prop :=
  HasClassCount (2 * d) d k ∧
  (∀ t ≤ d ^ 2, FailsAt d t ↔ t ∈ fails.map Prod.fst) ∧
  (∀ r ∈ fails, MaxIs d r.1 r.2.1 ∧ iCount (Kdd d) r.1 = r.2.2) ∧
  (∀ t ∈ uniq, UniqueMaxAt d t) ∧
  (∀ t ≤ d ^ 2, t ∉ fails.map Prod.fst → t ∉ uniq → TieMaxAt d t)

/-- **Table 2** and the text around it (§8). -/
def Table2 : Prop :=
  Table2Row 3 2 [(1, 28, 24)] [0, 2] ∧
  Table2Row 4 6 [(1, 61, 47), (3, 137, 127), (5, 187, 171)] [0, 4, 6] ∧
  Table2Row 5 60
    [(1, 116, 88), (2, 203, 188), (3, 321, 288), (5, 524, 448), (7, 679, 648), (8, 783, 748),
      (11, 908, 868)]
    [0, 4, 6, 9, 10, 12]

/-- §8: there are 70 cubic graphs on 6 labelled vertices. (Version 2: the count 19355 of
4-regular graphs on 8 labelled vertices is deleted.) -/
def LabelledCounts : Prop :=
  Nat.card {G : SimpleGraph (Fin 6) // G.IsRegularOfDegree 3} = 70

end Table2

open Classical in
/-- `G_n` (with `r = 0`, i.e. `k H_d` against `2k K_{d,d}`, `m = 2k`; canonical `u_k, w_k`)
wins at `(d, m, γ)`. -/
def DWins (d m : ℕ) [NeZero d] (γ : ℝ) : Prop :=
  iGamma (KddUnion m d) d γ < iGamma (Gn d m 0 0 0 0) d γ

open Classical in
/-- `G_n` loses at `(d, m, γ)`. -/
def DLoses (d m : ℕ) [NeZero d] (γ : ℝ) : Prop :=
  iGamma (Gn d m 0 0 0 0) d γ < iGamma (KddUnion m d) d γ

/-- The five values of `γ` at which the competitor wins at `n = 192`. -/
noncomputable def gammasWin192 : List ℝ :=
  [1 / 5, 1 / 4, 1 / 3, 2 / 5, 9 / 20]

/-- §8, "Other checks" for Theorem D (`n = 2dm` divisible by `4d`): at `n = 192`
(`m = 48, 32, 24` for `d = 2, 3, 4`) the competitor wins for `γ ∈ {1/5, 1/4, 1/3, 2/5, 9/20}` and
loses for `γ = 3/20`; for `d = 4`, `γ = 9/20` it loses at `n = 128, 208` (`m = 16, 26`); for
`d = 3`, `γ = 9/20` it wins at `n = 96, 192` (`m = 16, 32`) and loses at `n = 144` (`m = 24`);
for `γ = 3/20` it wins for every such `n` from 360 to 600 (`d = 2`), from 336 to 600 (`d = 3`)
and from 320 to 592 (`d = 4`). -/
def TheoremDNumerics : Prop :=
  (∀ γ ∈ gammasWin192, DWins 2 48 γ) ∧ DLoses 2 48 (3 / 20) ∧
  (∀ γ ∈ gammasWin192, DWins 3 32 γ) ∧ DLoses 3 32 (3 / 20) ∧
  (∀ γ ∈ gammasWin192, DWins 4 24 γ) ∧ DLoses 4 24 (3 / 20) ∧
  DLoses 4 16 (9 / 20) ∧ DLoses 4 26 (9 / 20) ∧
  DWins 3 16 (9 / 20) ∧ DWins 3 32 (9 / 20) ∧ DLoses 3 24 (9 / 20) ∧
  (∀ n ∈ Icc 360 600, 8 ∣ n → DWins 2 (n / 4) (3 / 20)) ∧
  (∀ n ∈ Icc 336 600, 12 ∣ n → DWins 3 (n / 6) (3 / 20)) ∧
  (∀ n ∈ Icc 320 592, 16 ∣ n → DWins 4 (n / 8) (3 / 20))

end BackfillPaper3.Challenge
