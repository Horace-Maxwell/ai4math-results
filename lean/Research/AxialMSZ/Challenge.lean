import Mathlib

/-!
# Challenge statements: blocks, dominance and the non-annihilation graph of primitive axial algebras

Round-7 task `axial` (work folder `work/round7/axial/`).  This file contains ONLY definitions and
statements (`def … : Prop`); nothing here is proved except the four bilinearity side conditions
needed to *define* a product from structure constants (`structProduct`).  After independent review
the file is frozen by SHA-256; phase C proves every `def … : Prop` below and a `Check.lean` states
`theorem check_X : Challenge.X := …` for each of them.

**Version 2** (2026-09-27, Lean 4.34.1 / Mathlib v4.34.1 project `work/research-lean-v434`): the
fixes of the independent review `work/round7/axial/REVIEW-CHALLENGE.md` are applied to the reviewed
version 1 (SHA-256 `76caf8d5dbc90cf2b43d01a6c902dd4869b99e8129013b3f4b0b02c13bd30e5b`); every change
is listed in `work/round7/axial/DIFF-v2.md`.  Known-answer tests: `ChallengeTests.lean`.

## Sources (exact wording and locations in `work/round7/axial/CONTRACT.md`)

* [GS]  I. Gorshkov, S. Shpectorov, *Axial Algebras: Questions and Conjectures*, arXiv:2606.30048v1,
  §2 (Defs. 2.1, 2.3–2.5), §3.2: Definition 3.7 (block), Problem 3.8 (is each axial block
  indecomposable?), Problem 3.9 (can dominance be non-symmetric?), Definition 3.10
  (non-annihilation graph), Problem 3.11 (finest (direct) sum decomposition vs. connected
  components of Δ = [MS, Conjecture 3.16]), Problem 3.12 (simple Majorana algebras).
* [MSZ] A. Mamontov, S. Shpectorov, V. Zhelyabin, *Radicals in primitive axial algebras*,
  arXiv:2602.11984v1, §2–3 (Defs. 2.1–2.4, Def. 3.1 block, Def. 3.3 decomposable, Lemma 3.4,
  Cor. 3.5, Def. 3.6 dominance), §9 Questions 9.2, 9.3, Def. 9.4, Questions 9.5, 9.6.
* [MS]  J. McInroy, S. Shpectorov, *Axial algebras of Jordan and Monster type*, arXiv:2209.08043v1,
  Defs. 2.1–2.4, Def. 3.9 (Seress), Def. 3.11 (sum decomposition), Def. 3.15 (Δ), Conjecture 3.16.
* [KMS] S.M.S. Khasraw, J. McInroy, S. Shpectorov, *On the structure of axial algebras*,
  Trans. AMS 373 (2020), arXiv:1809.10132: Def. 2.1 (fusion law: finite, symmetric), Def. 5.1
  (sum of subalgebras), Def. 6.1 (Δ), Conjecture 6.2 (Monster type only — NOT addressed here).
* [KMP] I. Kaygorodov, C. Martín González, P. Páez-Guillán, *Central extensions of axial algebras*,
  arXiv:2211.00334 (2022), J. Algebra 662 (2025): 2-dimensional axial algebras `D(β)`.
* [Peng] B. Peng, *A two-dimensional counterexample to radical equality in primitive axial
  algebras*, arXiv:2608.28653v1 (2026).

## Modelling conventions

* A commutative non-associative algebra over a field `K` is a vector space `V` with a bilinear
  product `μ : V →ₗ[K] V →ₗ[K] V`, `μ u v = uv`, together with the hypothesis `IsCommutative μ`.
  Associativity and unitality are never assumed (as in all four sources).
* A fusion law is a subset `F ⊆ K` with a map `⋆`; we store `⋆` as `star : K → K → Set K`
  (only its values on `F × F` matter).  The general propositions of §2 range over fusion laws
  that are finite and symmetric (`FusionLaw.IsFiniteSymmetric`), as in [MS, §2.1] and
  [KMS, Def. 2.1]; nothing is said about Seress, graded or Monster-type laws.
  `A_λ(a)` is Mathlib's `Module.End.eigenspace (μ a) λ`,
  `A_Λ(a) = ⨆_{λ ∈ Λ} A_λ(a)` (the sum is automatically direct).  `A_∅(a) = 0`.
* Ideals are subspaces closed under multiplication by arbitrary elements (two-sided; the
  algebras are commutative anyway).  `gen μ X` (= ⟨⟨X⟩⟩) is the smallest subspace containing `X`
  and closed under the product; `block μ a` (= I_a) is the smallest ideal containing `a`.
* "Decomposable" follows [MSZ, §3] / [GS, after Def. 3.7]: the algebra is the sum of its proper
  ideals.  For a subalgebra `S` (used for blocks, Problem 3.8) the ideals are those *of `S`
  as an algebra*: subspaces `J ≤ S` with `S J ⊆ J` (not necessarily ideals of `V`).
* Sum decompositions follow [MS, Def. 3.11] / [KMS, Def. 5.1]: a set of pairwise annihilating
  subalgebras generating the algebra (a set, so that equal members are not required to
  annihilate each other; this makes "only trivial sum decompositions" at least as strong as the
  indexed-family version).
* The non-annihilation graph Δ(X) is `SimpleGraph.fromRel` of `uv ≠ 0` on the subtype `X`
  (for commutative `μ` this is exactly "distinct `a, b` adjacent iff `ab ≠ 0`").
* Concrete algebras live on `Fin n → ℚ` with the standard basis `e i = Pi.single i 1`;
  the product is given by structure constants `T i j = e_i e_j` (`structProduct`).
-/

set_option autoImplicit false

namespace AxialMSZ.Challenge

open Module

/-! ## 1. General notions (for an arbitrary field `K` and vector space `V`) -/

section General

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- The product `μ` is commutative: `uv = vu`. -/
def IsCommutative (μ : V →ₗ[K] V →ₗ[K] V) : Prop :=
  ∀ u v : V, μ u v = μ v u

end General

/-- A fusion law `(F, ⋆)` with `F ⊆ K` ([GS, Def. 2.1], [MSZ, Def. 2.1], [MS, Def. 2.1]).
Only the values of `star` on `carrier × carrier` are used. -/
structure FusionLaw (K : Type*) where
  /-- the set `F ⊆ K` of admissible eigenvalues -/
  carrier : Set K
  /-- the fusion rule `λ ⋆ μ ⊆ F` -/
  star : K → K → Set K

namespace FusionLaw

variable {K : Type*} [Field K]

/-- The extra conditions of [KMS, Def. 2.1]: `F` finite, `⋆` symmetric, values inside `F`. -/
def IsFiniteSymmetric (F : FusionLaw K) : Prop :=
  F.carrier.Finite ∧ (∀ l m : K, F.star l m = F.star m l) ∧
    ∀ l ∈ F.carrier, ∀ m ∈ F.carrier, F.star l m ⊆ F.carrier

/-- Seress fusion law ([KMS, §6.3], [MS, Def. 3.9]): `0 ∈ F` and `0 ⋆ λ ⊆ {λ}` for all `λ ∈ F`. -/
def IsSeress (F : FusionLaw K) : Prop :=
  (0 : K) ∈ F.carrier ∧ ∀ l ∈ F.carrier, F.star 0 l ⊆ {l}

end FusionLaw

section General

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- The eigenspace `A_λ(a) = {u | au = λu}` of `ad_a = μ a`. -/
def eigsp (μ : V →ₗ[K] V →ₗ[K] V) (a : V) (l : K) : Submodule K V :=
  Module.End.eigenspace (μ a) l

/-- `A_Λ(a) = ⊕_{λ ∈ Λ} A_λ(a)`; for `Λ = ∅` this is `0`. -/
def eigspSet (μ : V →ₗ[K] V →ₗ[K] V) (a : V) (Λ : Set K) : Submodule K V :=
  ⨆ l ∈ Λ, eigsp μ a l

/-- `a` is an `F`-axis ([GS, Def. 2.3], [MSZ, Def. 2.2], [MS, Def. 2.2], [KMS, Def. 2.2]):
a nonzero idempotent with `A = A_F(a)` (so `ad_a` is semisimple with all eigenvalues in `F`)
and `A_λ(a) A_μ(a) ⊆ A_{λ⋆μ}(a)` for all `λ, μ ∈ F`. -/
def IsAxis (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (a : V) : Prop :=
  a ≠ 0 ∧ μ a a = a ∧ eigspSet μ a F.carrier = ⊤ ∧
    ∀ l ∈ F.carrier, ∀ m ∈ F.carrier, ∀ u ∈ eigsp μ a l, ∀ v ∈ eigsp μ a m,
      μ u v ∈ eigspSet μ a (F.star l m)

/-- A primitive `F`-axis: an `F`-axis with `A_1(a) = ⟨a⟩` ([GS, Def. 2.4], [MSZ, Def. 2.3]). -/
def IsPrimitiveAxis (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (a : V) : Prop :=
  IsAxis F μ a ∧ eigsp μ a 1 = Submodule.span K {a}

/-- `S` is closed under the product (a subalgebra, not necessarily unital). -/
def IsSubalgebra (μ : V →ₗ[K] V →ₗ[K] V) (S : Submodule K V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, μ u v ∈ S

/-- `⟨⟨X⟩⟩`: the subalgebra generated by `X`. -/
def gen (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V) : Submodule K V :=
  sInf {S : Submodule K V | X ⊆ S ∧ IsSubalgebra μ S}

/-- `(V, X)` is a primitive `F`-axial algebra ([GS, Def. 2.5], [MSZ, Def. 2.4], [MS, Def. 2.4]):
the product is commutative, every `a ∈ X` is a primitive `F`-axis, and `X` generates. -/
def IsPrimitiveAxialAlgebra (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V) : Prop :=
  IsCommutative μ ∧ (∀ a ∈ X, IsPrimitiveAxis F μ a) ∧ gen μ X = ⊤

/-- `I` is an ideal of the algebra `(V, μ)`. -/
def IsIdeal (μ : V →ₗ[K] V →ₗ[K] V) (I : Submodule K V) : Prop :=
  ∀ u : V, ∀ v ∈ I, μ u v ∈ I ∧ μ v u ∈ I

/-- `J` is an ideal of the subalgebra `S` regarded as an algebra in its own right. -/
def IsIdealIn (μ : V →ₗ[K] V →ₗ[K] V) (S J : Submodule K V) : Prop :=
  J ≤ S ∧ ∀ u ∈ S, ∀ v ∈ J, μ u v ∈ J ∧ μ v u ∈ J

/-- The block `I_a` ([MSZ, Def. 3.1], [GS, Def. 3.7]): the smallest ideal containing `a`. -/
def block (μ : V →ₗ[K] V →ₗ[K] V) (a : V) : Submodule K V :=
  sInf {I : Submodule K V | IsIdeal μ I ∧ a ∈ I}

/-- The subalgebra `S` (as an algebra) is decomposable: it is the sum of its proper ideals. -/
def IsDecomposableSub (μ : V →ₗ[K] V →ₗ[K] V) (S : Submodule K V) : Prop :=
  sSup {J : Submodule K V | IsIdealIn μ S J ∧ J ≠ S} = S

/-- The algebra is decomposable ([MSZ, Def. 3.3]): it is the sum of its proper ideals. -/
def IsDecomposable (μ : V →ₗ[K] V →ₗ[K] V) : Prop :=
  IsDecomposableSub μ ⊤

/-- Simple algebra: nonzero product and no ideals other than `0` and the whole algebra. -/
def IsSimpleAlg (μ : V →ₗ[K] V →ₗ[K] V) : Prop :=
  (∃ u v : V, μ u v ≠ 0) ∧ ∀ I : Submodule K V, IsIdeal μ I → I = ⊥ ∨ I = ⊤

/-- The non-annihilation graph `Δ(X)` ([KMS, Def. 6.1], [MS, Def. 3.15], [MSZ, Def. 9.4],
[GS, Def. 3.10]): vertex set `X`, distinct `a, b` adjacent iff `ab ≠ 0` (symmetrised). -/
def nonAnnGraph (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V) : SimpleGraph X :=
  SimpleGraph.fromRel fun p q : X => μ (p : V) (q : V) ≠ 0

/-- A Frobenius form ([GS, Def. 2.6], [MSZ, Def. 2.7]): a bilinear form `β` with
`β (uv) w = β u (vw)` for all `u, v, w`. -/
def IsFrobeniusForm (μ : V →ₗ[K] V →ₗ[K] V) (β : V →ₗ[K] V →ₗ[K] K) : Prop :=
  ∀ u v w : V, β (μ u v) w = β u (μ v w)

/-- A sum decomposition ([MS, Def. 3.11], [KMS, Def. 5.1]): a set of subalgebras, pairwise
annihilating (distinct members multiply to `0`), which together generate the algebra. -/
def IsSumDecomposition (μ : V →ₗ[K] V →ₗ[K] V) (S : Set (Submodule K V)) : Prop :=
  (∀ B ∈ S, IsSubalgebra μ B) ∧
    (∀ B ∈ S, ∀ C ∈ S, B ≠ C → ∀ u ∈ B, ∀ v ∈ C, μ u v = 0) ∧
    gen μ (⋃ B ∈ S, (B : Set V)) = ⊤

/-- Every sum decomposition is trivial (one of its members is the whole algebra), i.e. the
finest sum decomposition is `A` itself. -/
def OnlyTrivialSumDecompositions (μ : V →ₗ[K] V →ₗ[K] V) : Prop :=
  ∀ S : Set (Submodule K V), IsSumDecomposition μ S → (⊤ : Submodule K V) ∈ S

/-- The subalgebras generated by distinct connected components of `Δ(X)` annihilate each other
(the operational form of [MS, Conjecture 3.16] stated right after it in [MS]). -/
def ComponentsAnnihilate (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V) : Prop :=
  ∀ C D : (nonAnnGraph μ X).ConnectedComponent, C ≠ D →
    ∀ u ∈ gen μ (Subtype.val '' C.supp), ∀ v ∈ gen μ (Subtype.val '' D.supp), μ u v = 0

end General

/-! ## 2. The conjecture / problem forms, as propositions about ALL primitive axial algebras

(Everything is stated for fields and spaces in `Type`, i.e. universe 0; a counterexample over `ℚ`
refutes these statements.) -/

/-- [MS, Conjecture 3.16] (general fusion law), in the survey's operational form: for every
primitive axial algebra `(A, X)`, the subalgebras generated by distinct connected components of
`Δ(X)` annihilate each other (so that they form a sum decomposition).  [Restricted, as
[MS, §2.1] and [KMS, Def. 2.1] do, to finite symmetric fusion laws, so that its negation refutes
the statement under every source's definition of a fusion law.] -/
def MS_Conjecture_3_16 : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    F.IsFiniteSymmetric → IsPrimitiveAxialAlgebra F μ X → ComponentsAnnihilate μ X

/-- [GS, Problem 3.11] / [MSZ, Question 9.5], read with the finest sum decomposition: if the only
sum decomposition is the trivial one, then `Δ(X)` is connected (the summands of the finest sum
decomposition correspond to the connected components of `Δ`).  [Restricted to finite symmetric
fusion laws, as in [MS, §2.1] and [KMS, Def. 2.1].] -/
def FinestSumDecomposition_connected : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    F.IsFiniteSymmetric → IsPrimitiveAxialAlgebra F μ X → OnlyTrivialSumDecompositions μ →
      (nonAnnGraph μ X).Connected

/-- [MSZ, text after Question 9.5]: "the issue is whether an indecomposable primitive axial algebra
can have a disconnected non-annihilation graph Δ"; the expected answer as a proposition.
[Restricted to finite symmetric fusion laws, as in [MS, §2.1] and [KMS, Def. 2.1].] -/
def Indecomposable_connected : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    F.IsFiniteSymmetric → IsPrimitiveAxialAlgebra F μ X → ¬ IsDecomposable μ →
      (nonAnnGraph μ X).Connected

/-- General-fusion-law analogue of [GS, Problem 3.12] (which is about simple *Majorana*
algebras): every simple primitive axial algebra has a connected non-annihilation graph.  This
is a weaker consequence of [MS, Conj. 3.16], not a reading of it; [GS, Problem 3.12] itself is
not addressed.  [Restricted to finite symmetric fusion laws, as in [MS, §2.1] and
[KMS, Def. 2.1].] -/
def Simple_connected : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    F.IsFiniteSymmetric → IsPrimitiveAxialAlgebra F μ X → IsSimpleAlg μ →
      (nonAnnGraph μ X).Connected

/-- [GS, Problem 3.8] / [MSZ, Question 9.2]: every axial block `I_a` (`a ∈ X`) is
indecomposable as an algebra (with the ideals of the block itself).  The block need not itself be
an axial algebra ([MSZ] l. 373–375): e.g. in `ExD` the block `I_a` is not generated by the axes
`X ∩ I_a = {a, b}`.  [Restricted to finite symmetric fusion laws, as in [MS, §2.1] and
[KMS, Def. 2.1].] -/
def Blocks_indecomposable : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    F.IsFiniteSymmetric → IsPrimitiveAxialAlgebra F μ X →
      ∀ a ∈ X, ¬ IsDecomposableSub μ (block μ a)

/-- [GS, Problem 3.9] / [MSZ, Question 9.3], positive answer: there is a primitive axial algebra
with a proper inclusion `I_a ⊊ I_b` of blocks of two generating axes.  Already implicit in known
2-dimensional algebras: [KMP] (`D(β)`, `X = {e₁, e₂}`, 2022) and [Peng] (2026); see `ExP`.
[The fusion law is required to be finite and symmetric, as in [MS, §2.1] and [KMS, Def. 2.1].] -/
def Dominance_nonsymmetric : Prop :=
  ∃ (K : Type) (_ : Field K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    F.IsFiniteSymmetric ∧ IsPrimitiveAxialAlgebra F μ X ∧
      ∃ a ∈ X, ∃ b ∈ X, block μ a < block μ b

/-! ## 3. Fusion laws used by the examples -/

section Laws

variable {K : Type*} [Field K] [DecidableEq K]

/-- `J⁺(η)` on `{1, 0, η}`: the Jordan-type law `J(η)` of [GS, Fig. 4] except that `0 ⋆ 0` and
`0 ⋆ η` are enlarged to `{1, 0, η}`.  Table (blank = `∅`):
```
  ⋆ |  1    0       η
  1 |  1            η
  0 |      1,0,η   1,0,η
  η |  η   1,0,η   1,0
``` -/
def JPlus (η : K) : FusionLaw K where
  carrier := {1, 0, η}
  star l m :=
    if l = 1 then (if m = 0 then ∅ else {m})
    else if m = 1 then (if l = 0 then ∅ else {l})
    else if l = 0 ∨ m = 0 then {1, 0, η}
    else {1, 0}

/-- `J°(η)` on `{1, 0, η}`: `J(η)` except `0 ⋆ 0 = {0, η}` and `0 ⋆ η = {0, η}`.  Table:
```
  ⋆ |  1    0      η
  1 |  1           η
  0 |      0,η    0,η
  η |  η   0,η    1,0
``` -/
def JMild (η : K) : FusionLaw K where
  carrier := {1, 0, η}
  star l m :=
    if l = 1 then (if m = 0 then ∅ else {m})
    else if m = 1 then (if l = 0 then ∅ else {l})
    else if l = 0 ∨ m = 0 then {0, η}
    else {1, 0}

end Laws

/-- The fusion law `F_{D3}` at `β = -1` used by Bo Peng (arXiv:2608.28653, Table 1) and by
Kaygorodov–Martín González–Páez-Guillán (arXiv:2211.00334): on `{0, 1, 2}`,
`0⋆0 = {0,1}`, `1⋆1 = {1}`, `1⋆2 = 2⋆1 = 2⋆2 = {2}`, all other entries `∅`. -/
def FD3 : FusionLaw ℚ where
  carrier := {0, 1, 2}
  star l m :=
    if l = 0 ∧ m = 0 then {0, 1}
    else if l = 1 ∧ m = 1 then {1}
    else if (l = 1 ∧ m = 2) ∨ (l = 2 ∧ m = 1) ∨ (l = 2 ∧ m = 2) then {2}
    else ∅

/-! ## 4. Algebras given by structure constants -/

/-- The bilinear product on `Fin n → K` with structure constants `T` (`T i j = e_i e_j`):
`uv = ∑ i, ∑ j, (u i * v j) • T i j`. -/
def structProduct {K : Type*} [Field K] {n : ℕ} (T : Fin n → Fin n → (Fin n → K)) :
    (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] (Fin n → K) :=
  LinearMap.mk₂ K (fun u v => ∑ i, ∑ j, (u i * v j) • T i j)
    (by
      intro u₁ u₂ v
      simp only [Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib])
    (by
      intro c u v
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, mul_assoc])
    (by
      intro u v₁ v₂
      simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib])
    (by
      intro c u v
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring_nf)

/-- Standard basis vector `e i`. -/
abbrev e {n : ℕ} (i : Fin n) : Fin n → ℚ := Pi.single i 1

/-! ### Example S (simple, disconnected Δ): basis `a = e 0, b = e 1, x = e 2, c = e 3`, η = 1/2.
`(a, b, x)` span the Matsuo algebra 3C(1/2): `ab = ¼(a+b−x)`, `ax = ¼(a+x−b)`, `bx = ¼(b+x−a)`,
`a² = a`, `b² = b`, `x² = x`; `c² = c`, `ca = cb = 0`, `cx = ½(x−a−b) − ¼c`.  `X = {a, b, c}`. -/
namespace ExS

/-- structure constants of `S` (`T i j = e_i e_j`, coordinates w.r.t. `a, b, x, c`). -/
def T : Fin 4 → Fin 4 → (Fin 4 → ℚ) :=
  ![![![1, 0, 0, 0], ![1/4, 1/4, -1/4, 0], ![1/4, -1/4, 1/4, 0], ![0, 0, 0, 0]],
    ![![1/4, 1/4, -1/4, 0], ![0, 1, 0, 0], ![-1/4, 1/4, 1/4, 0], ![0, 0, 0, 0]],
    ![![1/4, -1/4, 1/4, 0], ![-1/4, 1/4, 1/4, 0], ![0, 0, 1, 0], ![-1/2, -1/2, 1/2, -1/4]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![-1/2, -1/2, 1/2, -1/4], ![0, 0, 0, 1]]]

/-- the product of `S` -/
def μ : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) := structProduct T

/-- the generating axes `{a, b, c}` -/
def X : Set (Fin 4 → ℚ) := {e 0, e 1, e 3}

/-- Main statement for `S`: a primitive `J⁺(1/2)`-axial algebra which is simple, whose
non-annihilation graph is disconnected, whose finest sum decomposition is trivial, and in which
the subalgebras generated by the two components of `Δ` do not annihilate each other. -/
def Statement : Prop :=
  IsPrimitiveAxialAlgebra (JPlus (1/2 : ℚ)) μ X ∧ IsSimpleAlg μ ∧
    ¬ (nonAnnGraph μ X).Connected ∧ OnlyTrivialSumDecompositions μ ∧ ¬ ComponentsAnnihilate μ X

end ExS

/-! ### Example E (the scout's example; non-symmetric dominance): basis `a, b, x, c`, η = 1/3.
3C(1/3) on `(a, b, x)`: `ab = ⅙(a+b−x)`, `ax = ⅙(a+x−b)`, `bx = ⅙(b+x−a)`; `c² = c`,
`ca = cb = 0`, `cx = ⅓(x−a−b)`.  `X = {a, b, c}`. -/
namespace ExE

/-- structure constants of `E` -/
def T : Fin 4 → Fin 4 → (Fin 4 → ℚ) :=
  ![![![1, 0, 0, 0], ![1/6, 1/6, -1/6, 0], ![1/6, -1/6, 1/6, 0], ![0, 0, 0, 0]],
    ![![1/6, 1/6, -1/6, 0], ![0, 1, 0, 0], ![-1/6, 1/6, 1/6, 0], ![0, 0, 0, 0]],
    ![![1/6, -1/6, 1/6, 0], ![-1/6, 1/6, 1/6, 0], ![0, 0, 1, 0], ![-1/3, -1/3, 1/3, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![-1/3, -1/3, 1/3, 0], ![0, 0, 0, 1]]]

/-- the product of `E` -/
def μ : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) := structProduct T

/-- the generating axes `{a, b, c}` -/
def X : Set (Fin 4 → ℚ) := {e 0, e 1, e 3}

/-- Main statement for `E`: a primitive `J⁺(1/3)`-axial algebra with `I_a = I_b ⊊ I_c = E`,
which is indecomposable and has a disconnected non-annihilation graph. -/
def Statement : Prop :=
  IsPrimitiveAxialAlgebra (JPlus (1/3 : ℚ)) μ X ∧
    block μ (e 0) < block μ (e 3) ∧ block μ (e 0) = block μ (e 1) ∧ block μ (e 3) = ⊤ ∧
    ¬ IsDecomposable μ ∧ ¬ (nonAnnGraph μ X).Connected ∧ ¬ ComponentsAnnihilate μ X

end ExE

/-! ### Example D (a decomposable block): basis `a, b, x, c, d` of `Fin 5 → ℚ`, η = 1/2.
3C(1/2) on `(a, b, x)` as in `S`; `c² = c`, `ca = cb = 0`, `cx = d`, `cd = ½d`, `d² = 0`,
`da = db = dx = 0`.  `X = {a, b, c}`.  The block `I_a = ⟨a, b, x, d⟩` is the sum of its proper
ideals `⟨a, b, x⟩` and `⟨d⟩` (ideals of `I_a`; the summand `⟨a, b, x⟩` is not an ideal of `D`,
and `I_a` is not generated by the axes `X ∩ I_a = {a, b}`). -/
namespace ExD

/-- structure constants of `D` (coordinates w.r.t. `a, b, x, c, d`) -/
def T : Fin 5 → Fin 5 → (Fin 5 → ℚ) :=
  ![![![1, 0, 0, 0, 0], ![1/4, 1/4, -1/4, 0, 0], ![1/4, -1/4, 1/4, 0, 0], ![0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0]],
    ![![1/4, 1/4, -1/4, 0, 0], ![0, 1, 0, 0, 0], ![-1/4, 1/4, 1/4, 0, 0], ![0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0]],
    ![![1/4, -1/4, 1/4, 0, 0], ![-1/4, 1/4, 1/4, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0]],
    ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 1/2]],
    ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 1/2],
      ![0, 0, 0, 0, 0]]]

/-- the product of `D` -/
def μ : (Fin 5 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) := structProduct T

/-- the generating axes `{a, b, c}` -/
def X : Set (Fin 5 → ℚ) := {e 0, e 1, e 3}

/-- Main statement for `D`: a primitive `J°(1/2)`-axial algebra whose block `I_a` is
decomposable (explicitly `I_a = ⟨a,b,x⟩ + ⟨d⟩` with both summands proper ideals of `I_a`), and
which admits a Frobenius form with `β a a ≠ 0` for every generating axis `a` (the non-singularity
condition under which [MSZ, Thm. 1.1 and l. 103–105] give `R(A) = J(A) = A^⊥`; the hypothesis of
[MSZ, Thm. 1.1] itself is only the existence of a Frobenius form, possibly zero). The block `I_a`
is not generated by the axes `X ∩ I_a = {a, b}`. -/
def Statement : Prop :=
  IsPrimitiveAxialAlgebra (JMild (1/2 : ℚ)) μ X ∧ IsDecomposableSub μ (block μ (e 0)) ∧
    (∃ β : (Fin 5 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) →ₗ[ℚ] ℚ, IsFrobeniusForm μ β ∧ ∀ a ∈ X, β a a ≠ 0) ∧
    block μ (e 0) = Submodule.span ℚ {e 0, e 1, e 2, e 4} ∧
    IsIdealIn μ (block μ (e 0)) (Submodule.span ℚ {e 0, e 1, e 2}) ∧
    IsIdealIn μ (block μ (e 0)) (Submodule.span ℚ {e 4}) ∧
    ¬ IsIdeal μ (Submodule.span ℚ {e 0, e 1, e 2})

end ExD

/-! ### Example P (Peng, arXiv:2608.28653; Kaygorodov–Martín González–Páez-Guillán `D(-1)`):
basis `a = e 0, b = e 1`; `a² = a`, `ab = 2b`, `b² = b`; `X = {a, b}`.  Known algebra; recorded
because its blocks `I_b = ⟨b⟩ ⊊ I_a = A` already answer [GS, Problem 3.9] (not stated there).
The entry `D(β)`, `X = {e₁, e₂}` of the 2-dimensional classification [KMP] (2022) has the same
feature (`⟨e₂⟩` is an ideal). -/
namespace ExP

/-- structure constants of Peng's algebra -/
def T : Fin 2 → Fin 2 → (Fin 2 → ℚ) :=
  ![![![1, 0], ![0, 2]],
    ![![0, 2], ![0, 1]]]

/-- the product -/
def μ : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := structProduct T

/-- the generating axes `{a, b}` -/
def X : Set (Fin 2 → ℚ) := {e 0, e 1}

/-- Peng's algebra is a primitive `F_{D3}`-axial algebra with `I_b ⊊ I_a`. -/
def Statement : Prop :=
  IsPrimitiveAxialAlgebra FD3 μ X ∧ block μ (e 1) < block μ (e 0)

end ExP

/-! ## 5. Statements to be proved in phase C -/

/-- The fusion laws used are well formed in the sense of [KMS] (finite, symmetric) and are not
Seress (so the partial results of [KMS, Thm. 6.14] and [HSS] do not apply). -/
def Laws_facts : Prop :=
  (JPlus (1/2 : ℚ)).IsFiniteSymmetric ∧ (JPlus (1/3 : ℚ)).IsFiniteSymmetric ∧
    (JMild (1/2 : ℚ)).IsFiniteSymmetric ∧ FD3.IsFiniteSymmetric ∧
    ¬ (JPlus (1/2 : ℚ)).IsSeress ∧ ¬ (JPlus (1/3 : ℚ)).IsSeress ∧ ¬ (JMild (1/2 : ℚ)).IsSeress

/-- Theorem A (main): the simple example `S`. -/
def TheoremA : Prop := ExS.Statement

/-- Theorem B: the example `E` (non-symmetric dominance inside an indecomposable algebra with
disconnected `Δ`).  A further example only: non-symmetric dominance is already implicit in
[KMP] and [Peng] (see `ExP`). -/
def TheoremB : Prop := ExE.Statement

/-- Theorem C: the example `D` (a decomposable block). -/
def TheoremC : Prop := ExD.Statement

/-- Remark (Peng / KMP algebra). -/
def RemarkP : Prop := ExP.Statement

/-- Corollary: the general forms (arbitrary finite symmetric fusion laws) of [MS, Conj. 3.16],
[GS, Problem 3.11]/[MSZ, Q. 9.5] (readings (R1)–(R3)), the general-law analogue of
[GS, Problem 3.12] (R4) are false, [GS, Problem 3.8] has a negative answer and [GS, Problem 3.9]
a positive one (the latter already implicit in [KMP]/Peng). -/
def Corollary : Prop :=
  ¬ MS_Conjecture_3_16 ∧ ¬ FinestSumDecomposition_connected ∧ ¬ Indecomposable_connected ∧
    ¬ Simple_connected ∧ ¬ Blocks_indecomposable ∧ Dominance_nonsymmetric

end AxialMSZ.Challenge
