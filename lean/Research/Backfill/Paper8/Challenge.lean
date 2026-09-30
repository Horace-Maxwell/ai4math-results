import Mathlib

/-!
# Challenge statements for paper 8 (Lean back-fill), version 2

Paper: H. Dong, *The switching conjecture for main eigenvalues holds for trees of diameter at
most 4*, release v1.7.0, `papers/switching-diam4/note.tex`.

This file contains ONLY definitions and statements (`def … : Prop`).  Nothing here is proved.
After independent review it is frozen by SHA-256; phase 2 proves every `def … : Prop` below and
`Check.lean` states `theorem check_X : Challenge.X := …` for each of them.

Numbering follows the paper (the theorem environments share one counter per section):
Lemma 2.1 (`lem:good`), Lemma 2.2 (`lem:krylov`), Lemma 3.1 (`lem:spec`), Lemma 3.2 (`lem:main`),
Lemma 3.3 (`lem:orbits`), Lemma 3.4 (`lem:equal`), Lemma 4.1 (`lem:real`), Lemma 4.2
(`lem:leafrow`), Lemma 4.3 (`lem:barerow`), Corollary 4.4 (`cor:criteria`), Proposition 5.1
(`prop:small`), Lemma 5.2 (`lem:count`), Proposition 5.3 (`prop:large`), Lemma 5.4
(`lem:region`), Proposition 5.5 (`prop:search`), Proposition 5.6 (`prop:three`), Theorem 1,
Remark 8.3 (`rem:regular`, already formalized in `Research/SwitchingWalkProfile.lean`).
Unnumbered claims of the text that the proofs use are stated as well (`TreeStructure`,
`Secular_monic`, `StdLeafSums`).

Modelling conventions (details in `work/lean-backfill/paper8/STATEMENTS.md`):
* matrices are real, indexed by a finite type; eigenvalues are real eigenvalues (all eigenvalues
  of a real symmetric matrix are real); a *switching* is `s : V → ℝ` with values `±1`;
* `P_θ s ≠ 0` uses Mathlib's orthogonal projection (`Submodule.starProjection`) of Euclidean
  space onto the eigenspace `E_θ`;
* the tree `T(a)` is built on the vertex type `Option (Σ i : Fin k, Option (Fin (a i)))`:
  `none` is the centre `c`, `some ⟨i, none⟩` is `v_i`, `some ⟨i, some j⟩` is the `j`-th leaf of
  branch `i`; the multiset of the paper is represented by the tuple `a : Fin k → ℕ`, and all
  numerical data (`B`, `k_b`, `r`, `b*`, `R`, `N_I`, `N_II`, `N_ei`, `ℒ_β`) are functions of the
  multiset `branchMS a`;
* counts of possibly-infinite sets of *parameters* use `Set.encard` (so that an infinite set
  could never satisfy a bound); counts of orbits/pairs use `Set.ncard` together with explicit
  finiteness statements (Lemma 3.3(d)).

## Version 2

Version 1 (SHA-256 `4fe68753c6151791fe601d4d8e5935ae3e150a21469bb4d9cf4053a706574303`, 30
statements) was reviewed independently and accepted as faithful
(`work/lean-backfill/paper8/REVIEW-CHALLENGE.md`: 30 ACCEPT); no proofs were written against it.
Version 2 follows the rule that every claim of the corrected paper is proved in Lean and that
claims which are not proved are deleted from the paper. It keeps the 30 statements and every
definition of version 1 unchanged and adds eight statements at the end of the file:

* `GoodNeg` (§2: if `s` is good, so is `-s`);
* `DiamRadius` (§1: the trees of diameter at most 4 are the trees of radius at most 2);
* `Theorem1_signed` (§1: the signature version of the conjecture for these trees; review item
  M1, with the reviewer's text);
* `Lemma_U1` (every real root of `R` is at most `b* + k`; used, but not stated, by version 1 of
  the paper for the search range of the program of Proposition 5.5; the corrected paper states
  it);
* `Lemma_3_2_pointwise` (abstract and §1: a secular eigenvalue is main after a switching iff
  `G_s(θ) ≠ 0`; review of version 2, item O1);
* `Sharp_T15`, `Sharp_T18` (§6: the bounds of Lemma 4.2 are attained by `T(15)` and by
  `T(18,0,0)`; review item M4, with the existence of the row as in item O2 of the review of
  version 2);
* `Remark_8_2` (Remark 8.2; review item M2, with the reviewer's text).

The name `mirror` (review item D1) is kept, so that the 30 statements of version 1 stay
byte-identical. Version 2 has 38 statements.
-/

set_option autoImplicit false

open Matrix Polynomial

namespace BackfillPaper8.Challenge

/-! ## Section 1–2: switchings and main eigenvalues -/

section Spectral

variable {n : Type} [Fintype n] [DecidableEq n]

/-- `θ` is a (real) eigenvalue of the real square matrix `M`: Mathlib's
`Module.End.HasEigenvalue` for the linear map `Matrix.toLin' M` (an abbreviation only). -/
abbrev IsEigenvalue (M : Matrix n n ℝ) (θ : ℝ) : Prop :=
  Module.End.HasEigenvalue (Matrix.toLin' M) θ

/-- `θ` is a *main* eigenvalue of `M`: it is an eigenvalue and its eigenspace (Mathlib
`Module.End.eigenspace`) is not orthogonal to the all-ones vector, i.e. contains a vector with
nonzero coordinate sum. -/
def IsMainEigenvalue (M : Matrix n n ℝ) (θ : ℝ) : Prop :=
  IsEigenvalue M θ ∧ ∃ x ∈ Module.End.eigenspace (Matrix.toLin' M) θ, ∑ i, x i ≠ 0

/-- Every eigenvalue of `M` is main. -/
def AllEigenvaluesMain (M : Matrix n n ℝ) : Prop :=
  ∀ θ : ℝ, IsEigenvalue M θ → IsMainEigenvalue M θ

/-- A switching: a sign `±1` at each index (vertex). -/
def IsSwitching (s : n → ℝ) : Prop :=
  ∀ v, s v = 1 ∨ s v = -1

/-- `D_s A D_s`, the matrix of the switched signed graph when `A = A(G)`. -/
def switchMatrix (A : Matrix n n ℝ) (s : n → ℝ) : Matrix n n ℝ :=
  diagonal s * A * diagonal s

/-- `P_θ s ≠ 0`, where `P_θ` is the orthogonal projection of Euclidean space `ℝⁿ` onto the
eigenspace `E_θ` of `A` (Mathlib's `Submodule.starProjection`). -/
def ProjNe (A : Matrix n n ℝ) (θ : ℝ) (s : n → ℝ) : Prop :=
  (Module.End.eigenspace (Matrix.toEuclideanLin A) θ).starProjection
    (WithLp.toLp 2 s : EuclideanSpace ℝ n) ≠ 0

/-- `s` is *good* for `A`: `P_θ s ≠ 0` for every eigenvalue `θ` of `A`. -/
def IsGood (A : Matrix n n ℝ) (s : n → ℝ) : Prop :=
  ∀ θ : ℝ, IsEigenvalue A θ → ProjNe A θ s

end Spectral

/-- **Lemma 2.1** (`lem:good`). For a real symmetric `A` and a switching `s`, an eigenvalue `θ`
of `A` is a main eigenvalue of `D_s A D_s` iff `P_θ s ≠ 0`. -/
def Lemma_2_1 : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (A : Matrix n n ℝ), A.IsSymm →
    ∀ s : n → ℝ, IsSwitching s → ∀ θ : ℝ, IsEigenvalue A θ →
      (IsMainEigenvalue (switchMatrix A s) θ ↔ ProjNe A θ s)

/-- Consequence stated after Lemma 2.1: `s` is good for `A` iff every eigenvalue of `D_s A D_s`
is main (used to read Theorem 1 as "every such tree has a good switching"). -/
def Lemma_2_1_good : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (A : Matrix n n ℝ), A.IsSymm →
    ∀ s : n → ℝ, IsSwitching s → (IsGood A s ↔ AllEigenvaluesMain (switchMatrix A s))

/-- **Lemma 2.2** (`lem:krylov`, Krylov certificate). `A` symmetric integer matrix with `d`
distinct eigenvalues, `s ∈ ℤⁿ`, `K` the integer matrix with columns `s, As, …, A^{d-1}s`.
Then `rank_ℚ K` is the number of eigenvalues `θ` with `P_θ s ≠ 0`; in particular `s` is good if
`K` has rank `d` over `𝔽_p` for some prime `p`. -/
def Lemma_2_2 : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), A.IsSymm → ∀ s : Fin n → ℤ,
    let AR : Matrix (Fin n) (Fin n) ℝ := A.map (Int.cast : ℤ → ℝ)
    let sR : Fin n → ℝ := fun i => (s i : ℝ)
    let d : ℕ := {θ : ℝ | IsEigenvalue AR θ}.ncard
    let K : Matrix (Fin n) (Fin d) ℤ := Matrix.of fun i j => ((A ^ (j : ℕ)) *ᵥ s) i
    (K.map (Int.cast : ℤ → ℚ)).rank = {θ : ℝ | IsEigenvalue AR θ ∧ ProjNe AR θ sR}.ncard ∧
      ((∃ p : ℕ, p.Prime ∧ (K.map (Int.cast : ℤ → ZMod p)).rank = d) → IsGood AR sR)

/-! ## Section 3: the trees `T(a)` and their spectrum -/

/-- Vertices of `T(a)`: `none` = centre `c`; `some ⟨i, none⟩` = `v_i`;
`some ⟨i, some j⟩` = the `j`-th leaf of branch `i` (an element of `L_i`). -/
abbrev TV {k : ℕ} (a : Fin k → ℕ) : Type :=
  Option (Σ i : Fin k, Option (Fin (a i)))

/-- `parentB a x y = true` iff `x = c` and `y = v_i`, or `x = v_i` and `y ∈ L_i`. -/
def parentB {k : ℕ} (a : Fin k → ℕ) : TV a → TV a → Bool
  | none, some ⟨_, none⟩ => true
  | some ⟨i, none⟩, some ⟨i', some _⟩ => decide (i = i')
  | _, _ => false

/-- The tree `T(a)`: `c ~ v_i` for all `i`, and `v_i ~ ℓ` for `ℓ ∈ L_i`. -/
def treeT {k : ℕ} (a : Fin k → ℕ) : SimpleGraph (TV a) :=
  SimpleGraph.fromRel (fun x y => parentB a x y = true)

/-- Adjacency in `T(a)` is decidable (`x ≠ y ∧ (parent x y ∨ parent y x)`). -/
instance treeT.decAdj {k : ℕ} (a : Fin k → ℕ) : DecidableRel (treeT a).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ (parentB a x y = true ∨ parentB a y x = true)))

/-- The branch sizes as a multiset (the multiset `a` of the paper). -/
def branchMS {k : ℕ} (a : Fin k → ℕ) : Multiset ℕ :=
  Multiset.map a Finset.univ.val

/-- `B`, the set of distinct branch sizes. -/
def Bset (m : Multiset ℕ) : Finset ℕ := m.toFinset

/-- `k_b`, the number of branches of size `b` (`k_b = 0` if `b ∉ B`). -/
def kb (m : Multiset ℕ) (b : ℕ) : ℕ := m.count b

/-- `b* = max B` (`0` for the empty multiset, which never occurs for a tree). -/
def bstar (m : Multiset ℕ) : ℕ := (Bset m).sup id

/-- `I_b = {i : a_i = b}`. -/
def Ib {k : ℕ} (a : Fin k → ℕ) (b : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => a i = b)

/-- The secular polynomial
`R(t) = ∏_{b∈B} (t - b) - ∑_{b∈B} k_b ∏_{b'∈B∖{b}} (t - b')` (in `ℤ[t]`). -/
noncomputable def secular (m : Multiset ℕ) : ℤ[X] :=
  (∏ b ∈ Bset m, (X - C (b : ℤ))) -
    ∑ b ∈ Bset m, C (kb m b : ℤ) * ∏ b' ∈ (Bset m).erase b, (X - C (b' : ℤ))

/-- `θ` is a *secular* value: `R(θ²) = 0`. (By Lemma 3.1(i) these are the `2r` secular
eigenvalues `±√t_j`.) -/
def IsSecular (m : Multiset ℕ) (θ : ℝ) : Prop :=
  aeval (θ ^ 2) (secular m) = 0

/-- Unnumbered claim of Section 3: `R ∈ ℤ[t]` is monic of degree `r = |B|`. -/
def Secular_monic : Prop :=
  ∀ m : Multiset ℕ, m ≠ 0 → (secular m).Monic ∧ (secular m).natDegree = (Bset m).card

/-- Unnumbered claims of Section 3 (paragraph "Notation"): every tree with `n ≥ 3` vertices and
diameter at most 4 is (isomorphic to) some `T(a)` with `k ≥ 1`; conversely every `T(a)` with
`k ≥ 1` is a tree of diameter at most 4 with `n = 1 + k + ∑ a_i` vertices. -/
def TreeStructure : Prop :=
  (∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V), T.IsTree → T.ediam ≤ 4 →
      3 ≤ Fintype.card V → ∃ (k : ℕ) (a : Fin k → ℕ), 0 < k ∧ Nonempty (T ≃g treeT a)) ∧
  (∀ (k : ℕ) (a : Fin k → ℕ), 0 < k →
      (treeT a).IsTree ∧ (treeT a).ediam ≤ 4 ∧ Fintype.card (TV a) = 1 + k + ∑ i, a i)

/-- The eigenvector `x^θ` of Lemma 3.1(i): `x_c = 1`, `x_{v_i} = θ/(θ² - a_i)`,
`x_ℓ = 1/(θ² - a_i)` for `ℓ ∈ L_i`. -/
noncomputable def secVec {k : ℕ} (a : Fin k → ℕ) (θ : ℝ) : TV a → ℝ
  | none => 1
  | some ⟨i, none⟩ => θ / (θ ^ 2 - (a i : ℝ))
  | some ⟨i, some _⟩ => 1 / (θ ^ 2 - (a i : ℝ))

/-- The adjacency matrix `A = A(T(a))` over `ℝ`. -/
noncomputable def adjT {k : ℕ} (a : Fin k → ℕ) : Matrix (TV a) (TV a) ℝ :=
  (treeT a).adjMatrix ℝ

/-- **Lemma 3.1(i)** (`lem:spec`). `R` has `r` simple roots `t_1 < ⋯ < t_r` with
`b_j < t_j < b_{j+1}` (`j < r`) and `t_r > b_r`, so `t_j > 0` and `t_j ∉ B`; for each `j`, both
`θ = ±√t_j` are simple eigenvalues of `A` with eigenvector `x^θ` (the eigenspace is spanned by
`x^θ`, and `x^θ ≠ 0` as `x^θ_c = 1`). `b_1 < ⋯ < b_r` is the increasing enumeration of `B`. -/
def Lemma_3_1_i : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k →
    let m := branchMS a
    let r := (Bset m).card
    let bs : Fin r ↪o ℕ := (Bset m).orderEmbOfFin rfl
    ∃ t : Fin r → ℝ, StrictMono t ∧
      ((secular m).map (Int.castRingHom ℝ)).roots = Multiset.map t Finset.univ.val ∧
      (∀ j : Fin r, (bs j : ℝ) < t j) ∧
      (∀ (j : Fin r) (h : j.val + 1 < r), t j < (bs ⟨j.val + 1, h⟩ : ℝ)) ∧
      (∀ j : Fin r, 0 < t j ∧ ∀ b ∈ Bset m, t j ≠ (b : ℝ)) ∧
      (∀ (j : Fin r) (θ : ℝ), θ ^ 2 = t j →
        Module.End.eigenspace (Matrix.toLin' (adjT a)) θ = Submodule.span ℝ {secVec a θ})

/-- **Lemma 3.1(ii)**. For `b ∈ B`, `b ≥ 1`, `k_b ≥ 2`, both `θ = ±√b` are eigenvalues of
multiplicity `k_b - 1`, and `E_θ` consists of the vectors with `x_{v_i} = α_i`, `x_ℓ = α_i/θ`
(`ℓ ∈ L_i`, `i ∈ I_b`), `∑_{i∈I_b} α_i = 0`, all other coordinates `0`. Multiplicity is the
dimension of the eigenspace (for a symmetric matrix it equals the algebraic multiplicity). -/
def Lemma_3_1_ii : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k →
    ∀ b ∈ Bset (branchMS a), 1 ≤ b → 2 ≤ kb (branchMS a) b → ∀ θ : ℝ, θ ^ 2 = (b : ℝ) →
      (∀ x : TV a → ℝ, x ∈ Module.End.eigenspace (Matrix.toLin' (adjT a)) θ ↔
        (x none = 0 ∧
          (∀ i, a i ≠ b → x (some ⟨i, none⟩) = 0 ∧ ∀ j, x (some ⟨i, some j⟩) = 0) ∧
          (∀ i, a i = b → ∀ j, x (some ⟨i, some j⟩) = x (some ⟨i, none⟩) / θ) ∧
          ∑ i ∈ Ib a b, x (some ⟨i, none⟩) = 0)) ∧
      Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' (adjT a)) θ) =
        kb (branchMS a) b - 1

/-- **Lemma 3.1(iii)**. The kernel of `A`: if `k_0 ≥ 1`, the vectors with `x_c = 0`, with
`x_{v_i} = 0` and `∑_{ℓ∈L_i} x_ℓ = 0` whenever `a_i ≥ 1`, and `∑_{i∈I_0} x_{v_i} = 0`; if
`k_0 = 0`, the vectors with `x_{v_i} = 0` and `∑_{ℓ∈L_i} x_ℓ = -x_c` for every `i`. -/
def Lemma_3_1_iii : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k →
    (1 ≤ kb (branchMS a) 0 → ∀ x : TV a → ℝ, adjT a *ᵥ x = 0 ↔
      (x none = 0 ∧
        (∀ i, 1 ≤ a i → x (some ⟨i, none⟩) = 0 ∧ ∑ j, x (some ⟨i, some j⟩) = 0) ∧
        ∑ i ∈ Ib a 0, x (some ⟨i, none⟩) = 0)) ∧
    (kb (branchMS a) 0 = 0 → ∀ x : TV a → ℝ, adjT a *ᵥ x = 0 ↔
      ∀ i, x (some ⟨i, none⟩) = 0 ∧ ∑ j, x (some ⟨i, some j⟩) = -x none)

/-- **Lemma 3.1(iv)**. `A` has no other eigenvalues; hence it has
`d = 2r + 2|{b ∈ B : b ≥ 1, k_b ≥ 2}| + [ker A ≠ 0]` distinct eigenvalues. -/
def Lemma_3_1_iv : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k →
    let m := branchMS a
    (∀ θ : ℝ, IsEigenvalue (adjT a) θ ↔
      (IsSecular m θ ∨ (∃ b ∈ Bset m, 1 ≤ b ∧ 2 ≤ kb m b ∧ θ ^ 2 = (b : ℝ)) ∨
        (θ = 0 ∧ ∃ x : TV a → ℝ, x ≠ 0 ∧ adjT a *ᵥ x = 0))) ∧
    {θ : ℝ | IsEigenvalue (adjT a) θ}.ncard =
      2 * (Bset m).card + 2 * ((Bset m).filter (fun b => 1 ≤ b ∧ 2 ≤ kb m b)).card +
        {θ : ℝ | θ = 0 ∧ ∃ x : TV a → ℝ, x ≠ 0 ∧ adjT a *ᵥ x = 0}.ncard

/-! ### The effect of a switching -/

section SwitchData

variable {k : ℕ} (a : Fin k → ℕ)

/-- `s_c`. -/
def sc (s : TV a → ℝ) : ℝ := s none
/-- `σ_i = s(v_i)`. -/
def sig (s : TV a → ℝ) (i : Fin k) : ℝ := s (some ⟨i, none⟩)
/-- `λ_i = ∑_{ℓ ∈ L_i} s(ℓ)`, the leaf sum of branch `i` (`0` for a bare branch). -/
def lam (s : TV a → ℝ) (i : Fin k) : ℝ := ∑ j : Fin (a i), s (some ⟨i, some j⟩)
/-- `S_b = ∑_{i∈I_b} σ_i`. -/
def Sb (s : TV a → ℝ) (b : ℕ) : ℝ := ∑ i ∈ Ib a b, sig a s i
/-- `Λ_b = ∑_{i∈I_b} λ_i`. -/
def Lamb (s : TV a → ℝ) (b : ℕ) : ℝ := ∑ i ∈ Ib a b, lam a s i
/-- `A_b = s_c k_b + Λ_b`. -/
def Ab (s : TV a → ℝ) (b : ℕ) : ℝ := sc a s * (kb (branchMS a) b : ℝ) + Lamb a s b

/-- `G_s(θ) = ∑_{b∈B} (A_b + S_b θ)/(t - b)` with `t = θ²`. -/
noncomputable def Gs (s : TV a → ℝ) (θ : ℝ) : ℝ :=
  ∑ b ∈ Bset (branchMS a), (Ab a s b + Sb a s b * θ) / (θ ^ 2 - (b : ℝ))

/-- `P_s(t) = ∑_{b∈B} A_b/(t - b)` (Lemma 3.4). -/
noncomputable def Ps (s : TV a → ℝ) (t : ℝ) : ℝ :=
  ∑ b ∈ Bset (branchMS a), Ab a s b / (t - (b : ℝ))

/-- Condition (S) of Lemma 3.2: `G_s(θ) ≠ 0` for every secular eigenvalue `θ`. -/
def condS (s : TV a → ℝ) : Prop :=
  ∀ θ : ℝ, IsSecular (branchMS a) θ → Gs a s θ ≠ 0

/-- Condition (L) of Lemma 3.2: for `b ∈ B`, `b ≥ 1`, `k_b ≥ 2` and `θ = ±√b`, the numbers
`σ_i + λ_i/θ` (`i ∈ I_b`) are not all equal. -/
def condL (s : TV a → ℝ) : Prop :=
  ∀ b ∈ Bset (branchMS a), 1 ≤ b → 2 ≤ kb (branchMS a) b → ∀ θ : ℝ, θ ^ 2 = (b : ℝ) →
    ∃ i ∈ Ib a b, ∃ i' ∈ Ib a b, sig a s i + lam a s i / θ ≠ sig a s i' + lam a s i' / θ

/-- Condition (Z) of Lemma 3.2 (only if `0` is an eigenvalue).  "Leaves of both signs" is
`s ℓ ≠ s ℓ'` for two leaves of the branch; for `k_0 = 0`, when every `L_i` is
monochromatic its common sign is `ε_i = λ_i / a_i` (all `a_i ≥ 1` when `k_0 = 0`). -/
def condZ (s : TV a → ℝ) : Prop :=
  (∃ x : TV a → ℝ, x ≠ 0 ∧ adjT a *ᵥ x = 0) →
    (1 ≤ kb (branchMS a) 0 →
      (∃ i, 2 ≤ a i ∧ ∃ j j', s (some ⟨i, some j⟩) ≠ s (some ⟨i, some j'⟩)) ∨
        (∃ i ∈ Ib a 0, ∃ i' ∈ Ib a 0, sig a s i ≠ sig a s i')) ∧
    (kb (branchMS a) 0 = 0 →
      (∃ i, ∃ j j', s (some ⟨i, some j⟩) ≠ s (some ⟨i, some j'⟩)) ∨
        sc a s ≠ ∑ i, lam a s i / (a i : ℝ))

end SwitchData

/-- **Lemma 3.2** (`lem:main`). A switching `s` of `T(a)` is good iff (S), (L) and (Z) hold. -/
def Lemma_3_2 : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → ∀ s : TV a → ℝ, IsSwitching s →
    (IsGood (adjT a) s ↔ condS a s ∧ condL a s ∧ condZ a s)

/-! ### Orbits -/

/-- `R(x²) ∈ ℚ[x]`. -/
noncomputable def R2 (m : Multiset ℕ) : ℚ[X] :=
  expand ℚ 2 ((secular m).map (Int.castRingHom ℚ))

/-- `f` is a monic irreducible factor of `R(x²)` in `ℚ[x]`; its set of roots is an *orbit*. -/
def IsOrbitFactor (m : Multiset ℕ) (f : ℚ[X]) : Prop :=
  f.Monic ∧ Irreducible f ∧ f ∣ R2 m

/-- `f(-x) = f(x)`. -/
def IsEvenPoly (f : ℚ[X]) : Prop := f.comp (-X) = f

/-- The monic polynomial `±f(-x)` (sign `(-1)^{deg f}`), whose roots are the negatives of the
roots of `f`. -/
noncomputable def mirror (f : ℚ[X]) : ℚ[X] := C ((-1) ^ f.natDegree) * f.comp (-X)

/-- The non-even pairs `{f, ±f(-x)}` (as sets of two factors). -/
def nonEvenPairs (m : Multiset ℕ) : Set (Set ℚ[X]) :=
  {P | ∃ f, IsOrbitFactor m f ∧ ¬ IsEvenPoly f ∧ P = {f, mirror f}}

/-- `N_I`: the number of integer pairs (factors of degree 1). -/
noncomputable def NI (m : Multiset ℕ) : ℕ :=
  {P ∈ nonEvenPairs m | ∀ f ∈ P, f.natDegree = 1}.ncard

/-- `N_II`: the number of irrational pairs (factors of degree ≥ 2). -/
noncomputable def NII (m : Multiset ℕ) : ℕ :=
  {P ∈ nonEvenPairs m | ∀ f ∈ P, f.natDegree ≠ 1}.ncard

/-- `N_ei`: the number of roots of `R` that are even integers but not perfect squares. -/
noncomputable def Nei (m : Multiset ℕ) : ℕ :=
  {z : ℤ | (secular m).eval z = 0 ∧ Even z ∧ ¬ IsSquare z}.ncard

/-- `ℚ(t) ⊆ ℝ` for `t = θ²`. -/
noncomputable abbrev QAdj (t : ℝ) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({t} : Set ℝ)

/-- **Lemma 3.3(a)** (`lem:orbits`). If `f(-x) = f(x)` then `θ ∉ ℚ(t)`; the case
`f(-x) = -f(x)` does not occur. -/
def Lemma_3_3_a : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → ∀ f : ℚ[X], IsOrbitFactor (branchMS a) f →
    f.comp (-X) ≠ -f ∧ ∀ θ : ℝ, aeval θ f = 0 → IsEvenPoly f → θ ∉ QAdj (θ ^ 2)

/-- **Lemma 3.3(b)**. If `f(-x) ≠ f(x)`, then `θ ∈ ℚ(t)`, `±f(-x)` is another monic irreducible
factor of `R(x²)` whose orbit is the negative of the orbit of `f`; if `deg f = 1` then `θ ∈ ℤ`
and `t` is a perfect square that is a root of `R`; otherwise `t ∉ ℚ`. -/
def Lemma_3_3_b : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → ∀ f : ℚ[X], IsOrbitFactor (branchMS a) f →
    ¬ IsEvenPoly f →
      IsOrbitFactor (branchMS a) (mirror f) ∧ mirror f ≠ f ∧
      (mirror f).rootSet ℝ = (fun x => -x) '' f.rootSet ℝ ∧
      ∀ θ : ℝ, aeval θ f = 0 →
        θ ∈ QAdj (θ ^ 2) ∧
        (f.natDegree = 1 → ∃ q : ℤ, θ = (q : ℝ) ∧ (secular (branchMS a)).eval (q ^ 2) = 0) ∧
        (f.natDegree ≠ 1 → θ ^ 2 ∉ Set.range (algebraMap ℚ ℝ))

/-- **Lemma 3.3(c)**. If an integer root `z` of `R` is not a perfect square, then
`{√z, -√z}` is an even orbit: `x² - z` is a monic irreducible (even) factor of `R(x²)`. -/
def Lemma_3_3_c : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → ∀ z : ℤ, (secular (branchMS a)).eval z = 0 →
    ¬ IsSquare z →
      IsOrbitFactor (branchMS a) (X ^ 2 - C (z : ℚ)) ∧ IsEvenPoly (X ^ 2 - C (z : ℚ))

/-- **Lemma 3.3(d)**. `N_I + 2 N_II + N_ei ≤ r` (with the finiteness of the counted sets). -/
def Lemma_3_3_d : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k →
    (nonEvenPairs (branchMS a)).Finite ∧
    {z : ℤ | (secular (branchMS a)).eval z = 0 ∧ Even z ∧ ¬ IsSquare z}.Finite ∧
    NI (branchMS a) + 2 * NII (branchMS a) + Nei (branchMS a) ≤ (Bset (branchMS a)).card

/-- **Lemma 3.3(e)**. For every switching `s`, if `s` fails at an orbit `O` (i.e. `G_s(θ) = 0`
for some `θ ∈ O`), then `G_s` vanishes on all of `O`. -/
def Lemma_3_3_e : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → ∀ s : TV a → ℝ, IsSwitching s →
    ∀ f : ℚ[X], IsOrbitFactor (branchMS a) f →
      ∀ θ ∈ f.rootSet ℝ, ∀ θ' ∈ f.rootSet ℝ, Gs a s θ = 0 → Gs a s θ' = 0

/-- **Lemma 3.4** (`lem:equal`). If `σ_1 = ⋯ = σ_k = σ`, then `G_s(θ) = σθ + P_s(t)` with
`P_s(t) ∈ ℚ(t)` for every secular `θ`; `s` fails at no even orbit; and `s` fails at a non-even
pair (at one of its two orbits) iff `P_s(t) ∈ {θ, -θ}`, `θ` any root of the pair. -/
def Lemma_3_4 : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → ∀ s : TV a → ℝ, IsSwitching s → ∀ σ : ℝ,
    (∀ i, sig a s i = σ) →
      (∀ θ : ℝ, IsSecular (branchMS a) θ →
          Gs a s θ = σ * θ + Ps a s (θ ^ 2) ∧ Ps a s (θ ^ 2) ∈ QAdj (θ ^ 2)) ∧
      (∀ f : ℚ[X], IsOrbitFactor (branchMS a) f → IsEvenPoly f →
          ∀ θ ∈ f.rootSet ℝ, Gs a s θ ≠ 0) ∧
      (∀ f : ℚ[X], IsOrbitFactor (branchMS a) f → ¬ IsEvenPoly f →
          ∀ θ ∈ f.rootSet ℝ ∪ (mirror f).rootSet ℝ,
          ((∃ θ' ∈ f.rootSet ℝ ∪ (mirror f).rootSet ℝ, Gs a s θ' = 0) ↔
            (Ps a s (θ ^ 2) = θ ∨ Ps a s (θ ^ 2) = -θ)))

/-! ## Section 4: two rows of switchings -/

/-- Position of `i` in `I_{a_i}` (0-based), `I_b` ordered as a subset of `Fin k`. -/
def posIn {k : ℕ} (a : Fin k → ℕ) (i : Fin k) : ℕ :=
  (Finset.univ.filter (fun j => j < i ∧ a j = a i)).card

/-- The standard leaf sums `λ°_i`: for `b = 1`: `-1`, except `1` for the smallest `i ∈ I_1`
when `k_1 ≥ 2`; for odd `b ≥ 3`: `-1`, except that the two smallest `i ∈ I_b` get `1` and `-3`
when `k_b ≥ 2`; for even `b ≥ 2`: `0, -2, 0, -2, …` along `I_b`; `0` for a bare branch. -/
def lamStd {k : ℕ} (a : Fin k → ℕ) (i : Fin k) : ℤ :=
  if a i = 0 then 0
  else if a i = 1 then
    (if posIn a i = 0 ∧ 2 ≤ kb (branchMS a) 1 then 1 else -1)
  else if a i % 2 = 1 then
    (if 2 ≤ kb (branchMS a) (a i) ∧ posIn a i = 0 then 1
     else if 2 ≤ kb (branchMS a) (a i) ∧ posIn a i = 1 then -3 else -1)
  else (if posIn a i % 2 = 0 then 0 else -2)

/-- Unnumbered claims of Section 4 about the standard leaf sums: `|λ°_i| ≤ a_i`,
`λ°_i ≡ a_i (mod 2)`, (P1) for `b ≥ 1` with `k_b ≥ 2` the `λ°_i`, `i ∈ I_b`, are not all equal,
and (P2) for `b ≥ 2` the smallest `i ∈ I_b` has `|λ°_i| < b`. -/
def StdLeafSums : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ),
    (∀ i, 1 ≤ a i → |lamStd a i| ≤ (a i : ℤ) ∧ Even (lamStd a i - (a i : ℤ))) ∧
    (∀ b ∈ Bset (branchMS a), 1 ≤ b → 2 ≤ kb (branchMS a) b →
      ∃ i ∈ Ib a b, ∃ i' ∈ Ib a b, lamStd a i ≠ lamStd a i') ∧
    (∀ i, 2 ≤ a i → posIn a i = 0 → |lamStd a i| < (a i : ℤ))

/-- `Λ°_b = ∑_{i∈I_b} λ°_i`. -/
def LamStdB {k : ℕ} (a : Fin k → ℕ) (b : ℕ) : ℤ := ∑ i ∈ Ib a b, lamStd a i

/-- `U(t) = ∑_{b∈B, b≥1} Λ°_b/(t - b)`. -/
noncomputable def Ufun {k : ℕ} (a : Fin k → ℕ) (t : ℝ) : ℝ :=
  ∑ b ∈ (Bset (branchMS a)).filter (fun b => 1 ≤ b), (LamStdB a b : ℝ) / (t - (b : ℝ))

/-- `U_β(t) = U(t) - Λ°_β/(t - β)`. -/
noncomputable def Ubeta {k : ℕ} (a : Fin k → ℕ) (β : ℕ) (t : ℝ) : ℝ :=
  Ufun a t - (LamStdB a β : ℝ) / (t - (β : ℝ))

/-- `ℒ_β(k)`: the integers `Λ = ∑ λ_i` with `λ_1, …, λ_k ∈ {-β, -β+2, …, β}`, not all equal if
`k ≥ 2`, and, if `β ≥ 2`, with `|λ_i| < β` for some `i`. -/
def Lset (β k : ℕ) : Set ℤ :=
  {Λ | ∃ l : Fin k → ℤ, (∀ i, |l i| ≤ (β : ℤ) ∧ Even (l i - (β : ℤ))) ∧ ∑ i, l i = Λ ∧
    (2 ≤ k → ∃ i i', l i ≠ l i') ∧ (2 ≤ β → ∃ i, |l i| < (β : ℤ))}

/-- **Lemma 4.1** (`lem:real`, realizable leaf sums). -/
def Lemma_4_1 : Prop :=
  ∀ β k : ℕ, 1 ≤ β → 1 ≤ k →
    (2 ≤ β →
      Lset β k = {Λ : ℤ | Even (Λ - (k : ℤ) * β) ∧ |Λ| ≤ (k : ℤ) * β - 2 ∧
                          ¬ (β = 2 ∧ k = 2 ∧ Λ = 0)} ∧
      (Lset β k).ncard = k * β - 1 - (if β = 2 ∧ k = 2 then 1 else 0)) ∧
    (β = 1 → 2 ≤ k →
      Lset 1 k = {Λ : ℤ | Even (Λ - (k : ℤ)) ∧ |Λ| ≤ (k : ℤ) - 2} ∧ (Lset 1 k).ncard = k - 1) ∧
    (β = 1 → k = 1 → Lset 1 1 = {1, -1} ∧ (Lset 1 1).ncard = 2)

/-- Member `s_{ε,Λ}` of the leaf row of `β` (Lemma 4.2): `s_c = ε`, `σ_i = 1` for every branch,
`λ_i = λ°_i` for `a_i ≥ 1`, `i ∉ I_β`, and leaf sums on `I_β` as in Lemma 4.1 with total `Λ`. -/
def IsLeafRowMember {k : ℕ} (a : Fin k → ℕ) (β : ℕ) (ε Λ : ℤ) (s : TV a → ℝ) : Prop :=
  IsSwitching s ∧ sc a s = (ε : ℝ) ∧ (∀ i, sig a s i = 1) ∧
  (∀ i, 1 ≤ a i → a i ≠ β → lam a s i = (lamStd a i : ℝ)) ∧
  ∑ i ∈ Ib a β, lam a s i = (Λ : ℝ) ∧
  (2 ≤ kb (branchMS a) β → ∃ i ∈ Ib a β, ∃ i' ∈ Ib a β, lam a s i ≠ lam a s i') ∧
  (2 ≤ β → ∃ i ∈ Ib a β, |lam a s i| < (β : ℝ))

/-- `s` fails at the non-even pair of `f`: `G_s` vanishes at a root of `f` or of `±f(-x)`. -/
def FailsAtPair {k : ℕ} (a : Fin k → ℕ) (s : TV a → ℝ) (f : ℚ[X]) : Prop :=
  ∃ θ ∈ f.rootSet ℝ ∪ (mirror f).rootSet ℝ, Gs a s θ = 0

/-- `s` fails at the orbit of `f`. -/
def FailsAtOrbit {k : ℕ} (a : Fin k → ℕ) (s : TV a → ℝ) (f : ℚ[X]) : Prop :=
  ∃ θ ∈ f.rootSet ℝ, Gs a s θ = 0

/-- **Lemma 4.2** (`lem:leafrow`). Assume `b* ≥ 2`, `β ∈ B`, `β ≥ 1`. Members exist for all
`ε = ±1`, `Λ ∈ ℒ_β`; every member satisfies (L), (Z) and
`G(θ) = θ + ε + U_β(t) + Λ/(t - β)`; no member fails at an even orbit; for any choice of one
member per parameter, an integer pair makes at most four members fail (at most two for each
`ε`), an irrational pair at most two. -/
def Lemma_4_2 : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → 2 ≤ bstar (branchMS a) →
    ∀ β ∈ Bset (branchMS a), 1 ≤ β →
      let L := Lset β (kb (branchMS a) β)
      (∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ L, ∃ s, IsLeafRowMember a β ε Λ s) ∧
      (∀ (ε Λ : ℤ) (s : TV a → ℝ), IsLeafRowMember a β ε Λ s →
        condL a s ∧ condZ a s ∧
        (∀ θ : ℝ, IsSecular (branchMS a) θ →
          Gs a s θ = θ + ε + Ubeta a β (θ ^ 2) + Λ / (θ ^ 2 - β)) ∧
        (∀ f : ℚ[X], IsOrbitFactor (branchMS a) f → IsEvenPoly f → ¬ FailsAtOrbit a s f)) ∧
      (∀ mem : ℤ → ℤ → TV a → ℝ,
        (∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ L, IsLeafRowMember a β ε Λ (mem ε Λ)) →
        ∀ f : ℚ[X], IsOrbitFactor (branchMS a) f → ¬ IsEvenPoly f →
          (f.natDegree = 1 →
            (∀ ε ∈ ({1, -1} : Set ℤ),
              {Λ : ℤ | Λ ∈ L ∧ FailsAtPair a (mem ε Λ) f}.encard ≤ 2) ∧
            {p : ℤ × ℤ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ L ∧
              FailsAtPair a (mem p.1 p.2) f}.encard ≤ 4) ∧
          (f.natDegree ≠ 1 →
            {p : ℤ × ℤ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ L ∧
              FailsAtPair a (mem p.1 p.2) f}.encard ≤ 2))

/-- Member `s_{ε,m}` of the bare row (Lemma 4.3): `s_c = ε`, leaf sums `λ°_i` and `σ_i = 1` on
the branches with `a_i ≥ 1`, and `σ_i = -1` on exactly `mm` of the bare branches, `+1` on the
others. -/
def IsBareRowMember {k : ℕ} (a : Fin k → ℕ) (ε : ℤ) (mm : ℕ) (s : TV a → ℝ) : Prop :=
  IsSwitching s ∧ sc a s = (ε : ℝ) ∧
  (∀ i, 1 ≤ a i → sig a s i = 1 ∧ lam a s i = (lamStd a i : ℝ)) ∧
  ((Ib a 0).filter (fun i => sig a s i = -1)).card = mm

/-- **Lemma 4.3** (`lem:barerow`). Assume `b* ≥ 2` and `k_0 ≥ 1`. Members exist for `ε = ±1`,
`0 ≤ m ≤ k_0`; every member satisfies (L), (Z) and `G(θ) = ε + U(t) + θ - 2m/θ`; for any
choice of one member per parameter, an even orbit makes at most one member fail, and only if its
`t = θ²` is an even integer; an integer pair at most four; an irrational pair at most two. -/
def Lemma_4_3 : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → 2 ≤ bstar (branchMS a) → 1 ≤ kb (branchMS a) 0 →
    let k0 := kb (branchMS a) 0
    (∀ ε ∈ ({1, -1} : Set ℤ), ∀ mm ≤ k0, ∃ s, IsBareRowMember a ε mm s) ∧
    (∀ (ε : ℤ) (mm : ℕ) (s : TV a → ℝ), IsBareRowMember a ε mm s →
      condL a s ∧ condZ a s ∧
      ∀ θ : ℝ, IsSecular (branchMS a) θ →
        Gs a s θ = ε + Ufun a (θ ^ 2) + θ - 2 * (mm : ℝ) / θ) ∧
    (∀ mem : ℤ → ℕ → TV a → ℝ,
      (∀ ε ∈ ({1, -1} : Set ℤ), ∀ mm ≤ k0, IsBareRowMember a ε mm (mem ε mm)) →
      ∀ f : ℚ[X], IsOrbitFactor (branchMS a) f →
        (IsEvenPoly f →
          {p : ℤ × ℕ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ≤ k0 ∧
            FailsAtOrbit a (mem p.1 p.2) f}.encard ≤ 1 ∧
          ((∃ p : ℤ × ℕ, p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ≤ k0 ∧ FailsAtOrbit a (mem p.1 p.2) f) →
            ∃ z : ℤ, Even z ∧ ∀ θ ∈ f.rootSet ℝ, θ ^ 2 = (z : ℝ))) ∧
        (¬ IsEvenPoly f → f.natDegree = 1 →
          {p : ℤ × ℕ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ≤ k0 ∧
            FailsAtPair a (mem p.1 p.2) f}.encard ≤ 4) ∧
        (¬ IsEvenPoly f → f.natDegree ≠ 1 →
          {p : ℤ × ℕ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ≤ k0 ∧
            FailsAtPair a (mem p.1 p.2) f}.encard ≤ 2))

/-- Criterion (a′) at a given `β`: `|ℒ_β| ≥ 2 N_I + N_II + 1`. -/
def CritAat (m : Multiset ℕ) (β : ℕ) : Prop :=
  2 * NI m + NII m + 1 ≤ (Lset β (kb m β)).ncard

/-- Criterion (a′): `|ℒ_β| ≥ 2 N_I + N_II + 1` for some `β ∈ B`, `β ≥ 1`. -/
def CritA (m : Multiset ℕ) : Prop :=
  ∃ β ∈ Bset m, 1 ≤ β ∧ CritAat m β

/-- Criterion (b′): `k_0 ≥ 1` and `2(k_0 + 1) > 4 N_I + 2 N_II + N_ei`. -/
def CritB (m : Multiset ℕ) : Prop :=
  1 ≤ kb m 0 ∧ 4 * NI m + 2 * NII m + Nei m < 2 * (kb m 0 + 1)

/-- **Corollary 4.4** (`cor:criteria`). Let `b* ≥ 2`. If (a′) holds at `β`, some member of the
leaf row of `β` is good (for any choice of the members); if (b′) holds, some member of the bare
row is good. In particular `T(a)` has a good switching. -/
def Cor_4_4 : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → 2 ≤ bstar (branchMS a) →
    (∀ β ∈ Bset (branchMS a), 1 ≤ β → CritAat (branchMS a) β →
      ∀ mem : ℤ → ℤ → TV a → ℝ,
        (∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset β (kb (branchMS a) β),
          IsLeafRowMember a β ε Λ (mem ε Λ)) →
        ∃ ε ∈ ({1, -1} : Set ℤ), ∃ Λ ∈ Lset β (kb (branchMS a) β), IsGood (adjT a) (mem ε Λ)) ∧
    (CritB (branchMS a) →
      ∀ mem : ℤ → ℕ → TV a → ℝ,
        (∀ ε ∈ ({1, -1} : Set ℤ), ∀ mm ≤ kb (branchMS a) 0, IsBareRowMember a ε mm (mem ε mm)) →
        ∃ ε ∈ ({1, -1} : Set ℤ), ∃ mm ≤ kb (branchMS a) 0, IsGood (adjT a) (mem ε mm)) ∧
    (CritA (branchMS a) ∨ CritB (branchMS a) →
      ∃ s : TV a → ℝ, IsSwitching s ∧ IsGood (adjT a) s)

/-! ## Section 5: proof of Theorem 1 -/

/-- The switching of `T(a)` with sign `c` at the centre, `mid i` at `v_i` and `leafS i j` at the
`j`-th leaf of branch `i`. -/
def mkSw {k : ℕ} (a : Fin k → ℕ) (c : ℝ) (mid : Fin k → ℝ) (leafS : (i : Fin k) → Fin (a i) → ℝ) :
    TV a → ℝ
  | none => c
  | some ⟨i, none⟩ => mid i
  | some ⟨i, some j⟩ => leafS i j

/-- **Proposition 5.1** (`prop:small`). `T(a)` with `n ≥ 3` and `b* ≤ 1`: the listed switchings
are good. (a) star: `-1` on one leaf (two if `k_0 = 4`); (b) `k_1 = 1`, `k_0 ≥ 2`; (c) `k_1 ≥ 2`,
`k_0 ≥ 2`; (d) `k_0 = 1`: one of `s^±` (`s_c = ±1`, all `σ_i = 1`, leaf sums `λ°_i`);
(e) `k_0 = 0`: `s^+`. The choices "one leaf" are universally quantified. -/
def Prop_5_1 : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → (∀ i, a i ≤ 1) → 3 ≤ 1 + k + ∑ i, a i →
    let k0 := kb (branchMS a) 0
    let k1 := kb (branchMS a) 1
    (k1 = 0 → ∀ U : Finset (Fin k), U.card = (if k0 = 4 then 2 else 1) →
      IsGood (adjT a) (mkSw a 1 (fun i => if i ∈ U then -1 else 1) (fun _ _ => 1))) ∧
    (k1 = 1 → 2 ≤ k0 → ∀ i0 : Fin k, a i0 = 0 →
      IsGood (adjT a) (mkSw a 1 (fun i => if i = i0 then -1 else 1) (fun _ _ => -1))) ∧
    (2 ≤ k1 → 2 ≤ k0 → ∀ i0 i1 : Fin k, a i0 = 0 → a i1 = 1 →
      IsGood (adjT a)
        (mkSw a 1 (fun i => if i = i0 then -1 else 1) (fun i _ => if i = i1 then -1 else 1))) ∧
    (k0 = 1 → ∃ ε ∈ ({1, -1} : Set ℝ),
      IsGood (adjT a) (mkSw a ε (fun _ => 1) (fun i _ => (lamStd a i : ℝ)))) ∧
    (k0 = 0 → IsGood (adjT a) (mkSw a 1 (fun _ => 1) (fun i _ => (lamStd a i : ℝ))))

/-- `g = |{0, …, b*} ∖ B|`. -/
def gapCount (m : Multiset ℕ) : ℕ := ((Finset.range (bstar m + 1)) \ Bset m).card

/-- `sq(B, b*)`: the number of integers `q ≥ 1` with `q² ≤ b* - 1` and `q² ∉ B`. -/
def sqCountB (B : Finset ℕ) (bs : ℕ) : ℕ :=
  ((Finset.Icc 1 bs).filter (fun q => q ^ 2 ≤ bs - 1 ∧ q ^ 2 ∉ B)).card

/-- **Lemma 5.2** (`lem:count`). For `b* ≥ 1`: `r = b* + 1 - g`, `sq ≤ ⌊√(b* - 1)⌋`,
`sq ≤ g`, `N_I ≤ sq + 1` and `N_I + 2 N_II + N_ei ≤ r`. -/
def Lemma_5_2 : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → 1 ≤ bstar (branchMS a) →
    let m := branchMS a
    let sq := sqCountB (Bset m) (bstar m)
    (Bset m).card = bstar m + 1 - gapCount m ∧ sq ≤ Nat.sqrt (bstar m - 1) ∧ sq ≤ gapCount m ∧
    NI m ≤ sq + 1 ∧ NI m + 2 * NII m + Nei m ≤ (Bset m).card

/-- **Proposition 5.3** (`prop:large`). If `b* ≥ 13`, then (a′) holds with `β = b*`; hence
some member of the leaf row of `b*` is good (for any choice of the members). -/
def Prop_5_3 : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → 13 ≤ bstar (branchMS a) →
    let m := branchMS a
    let bs := bstar m
    bs ∈ Bset m ∧ CritAat m bs ∧
    ∀ mem : ℤ → ℤ → TV a → ℝ,
      (∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset bs (kb m bs), IsLeafRowMember a bs ε Λ (mem ε Λ)) →
      ∃ ε ∈ ({1, -1} : Set ℤ), ∃ Λ ∈ Lset bs (kb m bs), IsGood (adjT a) (mem ε Λ)

/-- `ν(B) = min(sq + 1, r)`. -/
def nuB (B : Finset ℕ) (bs : ℕ) : ℕ := min (sqCountB B bs + 1) B.card

/-- `M(B) = 2ν(B) + ⌊(r - ν(B))/2⌋`. -/
def MB (B : Finset ℕ) (bs : ℕ) : ℕ := 2 * nuB B bs + (B.card - nuB B bs) / 2

/-- The two conditions of Lemma 5.4 together with `2 ≤ b* ≤ 12`: membership in `ℛ`. -/
def InRegion (m : Multiset ℕ) : Prop :=
  2 ≤ bstar m ∧ bstar m ≤ 12 ∧
  (∀ β ∈ Bset m, 1 ≤ β → (Lset β (kb m β)).ncard ≤ MB (Bset m) (bstar m)) ∧
  (1 ≤ kb m 0 → 2 * (kb m 0 + 1) ≤ 3 * nuB (Bset m) (bstar m) + (Bset m).card)

/-- The region `ℛ` (a set of multisets of nonnegative integers). -/
def regionR : Set (Multiset ℕ) := {m | InRegion m}

/-- **Lemma 5.4** (`lem:region`). If `2 ≤ b* ≤ 12` and `T(a)` satisfies neither (a′) (for any
`β`) nor (b′), then `a ∈ ℛ`; `ℛ` is finite, has `13,376` elements, and each has `n ≤ 124`
(`n = 1 + |a| + ∑ a`). -/
def Lemma_5_4 : Prop :=
  (∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → 2 ≤ bstar (branchMS a) → bstar (branchMS a) ≤ 12 →
      ¬ CritA (branchMS a) → ¬ CritB (branchMS a) → InRegion (branchMS a)) ∧
  regionR.Finite ∧ regionR.ncard = 13376 ∧
  ∀ m ∈ regionR, 1 + Multiset.card m + m.sum ≤ 124

/-- **Proposition 5.5** (`prop:search`). Every multiset in `ℛ` except `(2,2)`, `(2,0,0)` and
`(3)` satisfies (a′) or (b′) (with the exact `N_I`, `N_II`, `N_ei`). -/
def Prop_5_5 : Prop :=
  ∀ m ∈ regionR, m ≠ {2, 2} → m ≠ {2, 0, 0} → m ≠ {3} → CritA m ∨ CritB m

/-- The switching of Proposition 5.6(a) on `T(2,2)`: `s_c = σ_1 = σ_2 = 1`, leaves of `v_1`
`+1, +1`, leaves of `v_2` `-1, -1`. -/
def sw56a : TV (![2, 2] : Fin 2 → ℕ) → ℝ :=
  mkSw ![2, 2] 1 (fun _ => 1) (fun i _ => if i = 0 then 1 else -1)

/-- The switching of Proposition 5.6(b) on `T(2,0,0) = D(2,2)`: `s_c = 1`, `+1` on the two leaf
neighbours `v_2, v_3` of `c`, `-1` on `v = v_1`, and `+1, -1` on the two leaves of `v_1`. -/
def sw56b : TV (![2, 0, 0] : Fin 3 → ℕ) → ℝ :=
  mkSw ![2, 0, 0] 1 (fun i => if i = 0 then -1 else 1) (fun _ j => if j.val = 0 then 1 else -1)

/-- The switching of Proposition 5.6(c) on `T(3) = K_{1,4}` rooted at a leaf `c`: `s_c = 1`,
`+1` on the star centre `v = v_1`, and `+1, -1, -1` on the other three leaves. -/
def sw56c : TV (![3] : Fin 1 → ℕ) → ℝ :=
  mkSw ![3] 1 (fun _ => 1) (fun _ j => if j.val = 0 then 1 else -1)

/-- **Proposition 5.6** (`prop:three`). The three switchings are good; the trees have `7`, `6`
and `5` vertices. -/
def Prop_5_6 : Prop :=
  (IsGood (adjT (![2, 2] : Fin 2 → ℕ)) sw56a ∧ Fintype.card (TV (![2, 2] : Fin 2 → ℕ)) = 7) ∧
  (IsGood (adjT (![2, 0, 0] : Fin 3 → ℕ)) sw56b ∧
    Fintype.card (TV (![2, 0, 0] : Fin 3 → ℕ)) = 6) ∧
  (IsGood (adjT (![3] : Fin 1 → ℕ)) sw56c ∧ Fintype.card (TV (![3] : Fin 1 → ℕ)) = 5)

/-- **Theorem 1.** Let `T` be a tree of diameter at most 4 other than `K_2`. Then some switching
`s` of `T` makes every eigenvalue of `T^s` main. -/
def Theorem1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → T.ediam ≤ 4 → IsEmpty (T ≃g (⊤ : SimpleGraph (Fin 2))) →
      ∃ s : V → ℝ, IsSwitching s ∧ AllEigenvaluesMain (switchMatrix (T.adjMatrix ℝ) s)

/-- Theorem 1 restated with Mathlib names only (no definition of this file): the trust surface
of this statement is Mathlib alone.  `Theorem1 ↔ Theorem1_mathlib` holds by unfolding. -/
def Theorem1_mathlib : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → T.ediam ≤ 4 → IsEmpty (T ≃g (⊤ : SimpleGraph (Fin 2))) →
      ∃ s : V → ℝ, (∀ v, s v = 1 ∨ s v = -1) ∧
        ∀ θ : ℝ,
          Module.End.HasEigenvalue (Matrix.toLin' (diagonal s * T.adjMatrix ℝ * diagonal s)) θ →
          ∃ x ∈ Module.End.eigenspace (Matrix.toLin' (diagonal s * T.adjMatrix ℝ * diagonal s)) θ,
            ∑ i, x i ≠ 0

/-! ## Section 8 -/

/-- **Remark 8.3** (`rem:regular`; not used for Theorem 1; formalized in v1.7.0 as
`SwitchingWalkProfile.main_after_switching`). `A` real symmetric of order `n ≠ 2` with constant
row sums `k`, `(A^j)_{vv} = ∑_u w_u (A^j)_{uu}` for all `j ≥ 0` with all `w_u > 0`: then
`s = 1 - 2e_v` is good for `A`. -/
def Remark_8_3 : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.IsSymm → ∀ c : ℝ,
    A *ᵥ (fun _ => (1 : ℝ)) = c • (fun _ => (1 : ℝ)) → Fintype.card ι ≠ 2 →
    ∀ (v : ι) (w : ι → ℝ), (∀ u, 0 < w u) → (∀ j : ℕ, (A ^ j) v v = ∑ u, w u * (A ^ j) u u) →
      IsGood A (fun i => if i = v then -1 else 1)

/-! ## Version 2 additions -/

/-- §2, after Lemma 2.1: if `s` is good for `A`, so is `-s`. -/
def GoodNeg : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (s : n → ℝ),
    IsGood A s → IsGood A (-s)

/-- §1: the trees of diameter at most 4 are the trees of radius at most 2 (Mathlib's
`SimpleGraph.ediam` and `SimpleGraph.radius`). -/
def DiamRadius : Prop :=
  ∀ (V : Type) [Fintype V] (T : SimpleGraph V), T.IsTree → (T.ediam ≤ 4 ↔ T.radius ≤ 2)

/-- §1: "Since every signature of a tree is a switching of the all-positive one, Theorem 1 also
gives the signature version of the conjecture [akmp, Conjecture 1.7] for these trees": for every
signature `σ` of `T` (a sign `±1` on each edge), some switching of the signed tree `(T, σ)` makes
every eigenvalue main. -/
def Theorem1_signed : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree → T.ediam ≤ 4 → IsEmpty (T ≃g (⊤ : SimpleGraph (Fin 2))) →
    ∀ σ : V → V → ℝ, (∀ u v, σ u v = σ v u) → (∀ u v, T.Adj u v → σ u v = 1 ∨ σ u v = -1) →
      ∃ s : V → ℝ, IsSwitching s ∧
        AllEigenvaluesMain (switchMatrix (Matrix.of fun u v => σ u v * T.adjMatrix ℝ u v) s)

/-- Bound on the roots of `R` (not stated in version 1 of the paper, whose program for
Proposition 5.5 used it for its search range `(b*, b* + k]`): every real root `t` of `R`
satisfies `t ≤ b* + k`. -/
def Lemma_U1 : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → ∀ t : ℝ, aeval t (secular (branchMS a)) = 0 →
    t ≤ (bstar (branchMS a) : ℝ) + k

/-- Abstract and §1 ("Method"), per-eigenvalue form of condition (S) of Lemma 3.2: for a
switching `s` of `T(a)` and a secular `θ`, `θ` is a main eigenvalue of `D_s A D_s` iff
`G_s(θ) ≠ 0` (review of version 2, item O1, with the reviewer's text). -/
def Lemma_3_2_pointwise : Prop :=
  ∀ (k : ℕ) (a : Fin k → ℕ), 0 < k → ∀ s : TV a → ℝ, IsSwitching s →
    ∀ θ : ℝ, IsSecular (branchMS a) θ →
      (IsMainEigenvalue (switchMatrix (adjT a) s) θ ↔ Gs a s θ ≠ 0)

/-- §6, sharpness of Lemma 4.2 for integer pairs: in `T(15)` a leaf row of `β = 15` exists, and
for every choice of its members the integer pair of `x - 4` makes exactly four members fail. -/
def Sharp_T15 : Prop :=
  IsOrbitFactor (branchMS (![15] : Fin 1 → ℕ)) (X - C 4) ∧ ¬ IsEvenPoly (X - C 4) ∧
  (∃ mem : ℤ → ℤ → TV (![15] : Fin 1 → ℕ) → ℝ,
    ∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset 15 1,
      IsLeafRowMember (![15] : Fin 1 → ℕ) 15 ε Λ (mem ε Λ)) ∧
  ∀ mem : ℤ → ℤ → TV (![15] : Fin 1 → ℕ) → ℝ,
    (∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset 15 1,
      IsLeafRowMember (![15] : Fin 1 → ℕ) 15 ε Λ (mem ε Λ)) →
    {p : ℤ × ℤ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ Lset 15 1 ∧
      FailsAtPair (![15] : Fin 1 → ℕ) (mem p.1 p.2) (X - C 4)}.encard = 4

/-- §6, sharpness of Lemma 4.2 for irrational pairs: in `T(18,0,0)` a leaf row of `β = 18`
exists, and for every choice of its members the irrational pair of `x² + 3x - 6` makes exactly
two members fail. -/
def Sharp_T18 : Prop :=
  IsOrbitFactor (branchMS (![18, 0, 0] : Fin 3 → ℕ)) (X ^ 2 + C 3 * X - C 6) ∧
  ¬ IsEvenPoly (X ^ 2 + C 3 * X - C 6) ∧ (X ^ 2 + C 3 * X - C 6 : ℚ[X]).natDegree ≠ 1 ∧
  (∃ mem : ℤ → ℤ → TV (![18, 0, 0] : Fin 3 → ℕ) → ℝ,
    ∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset 18 1,
      IsLeafRowMember (![18, 0, 0] : Fin 3 → ℕ) 18 ε Λ (mem ε Λ)) ∧
  ∀ mem : ℤ → ℤ → TV (![18, 0, 0] : Fin 3 → ℕ) → ℝ,
    (∀ ε ∈ ({1, -1} : Set ℤ), ∀ Λ ∈ Lset 18 1,
      IsLeafRowMember (![18, 0, 0] : Fin 3 → ℕ) 18 ε Λ (mem ε Λ)) →
    {p : ℤ × ℤ | p.1 ∈ ({1, -1} : Set ℤ) ∧ p.2 ∈ Lset 18 1 ∧
      FailsAtPair (![18, 0, 0] : Fin 3 → ℕ) (mem p.1 p.2) (X ^ 2 + C 3 * X - C 6)}.encard = 2

/-- **Remark 8.2** (`rem:G`; not used for Theorem 1). `G` bipartite with
`A = [[0, C], [Cᵀ, 0]]`, `θ ≠ 0` an eigenvalue whose minimal polynomial (over `ℚ`) is even, and
`s` rational: `P_θ s = 0 ↔ P_{-θ} s = 0`. -/
def Remark_8_2 : Prop :=
  ∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (C : Matrix m n ℝ),
    (∀ i j, C i j = 0 ∨ C i j = 1) → ∀ θ : ℝ, θ ≠ 0 →
    IsEigenvalue (Matrix.fromBlocks 0 C Cᵀ 0) θ → IsEvenPoly (minpoly ℚ θ) →
    ∀ s : m ⊕ n → ℚ,
      (ProjNe (Matrix.fromBlocks 0 C Cᵀ 0) θ (fun i => (s i : ℝ)) ↔
        ProjNe (Matrix.fromBlocks 0 C Cᵀ 0) (-θ) (fun i => (s i : ℝ)))

end BackfillPaper8.Challenge
