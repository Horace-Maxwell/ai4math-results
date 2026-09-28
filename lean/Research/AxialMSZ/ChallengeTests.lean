import Research.AxialMSZ.Challenge

/-!
# Known-answer tests for `AxialMSZ.Challenge` (version 2)

Seeded with the independent reviewer's probes (`work/round7/axial/review-challenge/
AxialReviewTests.lean` and `FixCheck.lean`), plus the additions the review recommends (FIX-3).
Every test is a small closed statement about the *definitions* of the challenge file; none of
them proves a `def … : Prop` of the challenge.  Groups:

1. fusion-law tables, including empty entries;
2. deliberately false instances (each must be *refuted*);
3. structure-constant spot checks;
4. semantics on toy algebras: `Split2 = ℚ ⊕ ℚ` is decomposable, has a non-trivial sum
   decomposition, is not simple and has a disconnected `Δ`; `One = ℚ` is simple and not
   decomposable;
5. the relation between the reviewed version 1 and version 2 of the general propositions.
-/

set_option autoImplicit false

namespace AxialMSZ.ChallengeTests

open AxialMSZ.Challenge

/-! ## 1. Fusion-law tables (reviewer's probes, plus further entries) -/

example : (JPlus (1/2 : ℚ)).star 0 0 = {1, 0, 1/2} := by simp [JPlus]
example : (JPlus (1/2 : ℚ)).star 0 (1/2) = {1, 0, 1/2} := by norm_num [JPlus]
example : (JPlus (1/2 : ℚ)).star (1/2) (1/2) = {1, 0} := by norm_num [JPlus]
example : (JPlus (1/2 : ℚ)).star 1 0 = ∅ := by simp [JPlus]
example : (JPlus (1/2 : ℚ)).star 1 (1/2) = {1/2} := by norm_num [JPlus]
example : (JPlus (1/2 : ℚ)).star 1 1 = {1} := by simp [JPlus]
example : (JPlus (1/3 : ℚ)).star (1/3) (1/3) = {1, 0} := by norm_num [JPlus]
example : (JPlus (1/3 : ℚ)).star 0 (1/3) = {1, 0, 1/3} := by norm_num [JPlus]
example : (JMild (1/2 : ℚ)).star 0 0 = {0, 1/2} := by simp [JMild]
example : (JMild (1/2 : ℚ)).star (1/2) 0 = {0, 1/2} := by norm_num [JMild]
example : (JMild (1/2 : ℚ)).star (1/2) (1/2) = {1, 0} := by norm_num [JMild]
example : (JMild (1/2 : ℚ)).star 0 1 = ∅ := by simp [JMild]
example : FD3.star 0 0 = {0, 1} := by norm_num [FD3]
example : FD3.star 0 2 = ∅ := by norm_num [FD3]
example : FD3.star 2 1 = {2} := by norm_num [FD3]
example : FD3.star 1 1 = {1} := by norm_num [FD3]
example : FD3.star 1 0 = ∅ := by norm_num [FD3]
example : (JPlus (1/2 : ℚ)).carrier = {1, 0, 1/2} := rfl

/-! ## 2. Deliberately false instances (each statement is refuted) -/

/-- `J⁺(½)` is not the Jordan law: `0 ⋆ 0 ≠ {0}`. -/
example : (JPlus (1/2 : ℚ)).star 0 0 ≠ {0} := by
  intro h
  have : (1 : ℚ) ∈ (JPlus (1/2 : ℚ)).star 0 0 := by simp [JPlus]
  rw [h] at this
  norm_num at this

/-- `J°(½)` is not the Jordan law either: `0 ⋆ 0 ≠ {0}`. -/
example : (JMild (1/2 : ℚ)).star 0 0 ≠ {0} := by
  intro h
  have : (1/2 : ℚ) ∈ (JMild (1/2 : ℚ)).star 0 0 := by simp [JMild]
  rw [h] at this
  norm_num at this

/-- `J⁺(½)` and `J°(½)` differ at `0 ⋆ 0` (`1 ∈ J⁺`, `1 ∉ J°`). -/
example : (JPlus (1/2 : ℚ)).star 0 0 ≠ (JMild (1/2 : ℚ)).star 0 0 := by
  intro h
  have h1 : (1 : ℚ) ∈ (JPlus (1/2 : ℚ)).star 0 0 := by simp [JPlus]
  rw [h] at h1
  simp [JMild] at h1

/-- An axis must be nonzero. -/
example : ¬ IsAxis (JPlus (1/2 : ℚ)) ExS.μ 0 := fun h => h.1 rfl

/-- `Dominance_nonsymmetric` cannot be met by `a = b`. -/
example : ¬ (block ExP.μ (e 0) < block ExP.μ (e 0)) := lt_irrefl _

/-- A non-symmetric law fails the new hypothesis `IsFiniteSymmetric` (so FIX-1 is not vacuous). -/
example :
    ¬ (⟨{0, 1}, fun l m => if l = 0 ∧ m = 1 then {0} else ∅⟩ : FusionLaw ℚ).IsFiniteSymmetric := by
  rintro ⟨-, hsym, -⟩
  have h := hsym 0 1
  simp at h

/-- The product `c·x` of `S` is not zero (the edge-free pair `c, x` of the counterexample). -/
example : ExS.μ (e 3) (e 2) ≠ 0 := by
  intro h
  have := congrFun h 3
  simp [ExS.μ, structProduct, ExS.T, Fin.sum_univ_four, e] at this

/-! ## 3. Structure constants (reviewer's spot checks, plus two more) -/

example : ExS.μ (e 3) (e 2) = ![-1/2, -1/2, 1/2, -1/4] := by
  ext k
  fin_cases k <;> simp [ExS.μ, structProduct, ExS.T, Fin.sum_univ_four, e]

example : ExE.μ (e 0) (e 1) = ![1/6, 1/6, -1/6, 0] := by
  ext k
  fin_cases k <;> simp [ExE.μ, structProduct, ExE.T, Fin.sum_univ_four, e]

example : ExD.μ (e 3) (e 2) = e 4 := by
  ext k
  fin_cases k <;> simp [ExD.μ, structProduct, ExD.T, Fin.sum_univ_five, e]

example : ExS.μ (e 3) (e 0) = 0 := by
  ext k
  fin_cases k <;> simp [ExS.μ, structProduct, ExS.T, Fin.sum_univ_four, e]

example : ExP.μ (e 0) (e 1) = ![0, 2] := by
  ext k
  fin_cases k <;> simp [ExP.μ, structProduct, ExP.T, Fin.sum_univ_two, e]

/-! ## 4. Semantics on toy algebras -/

/-! ### `Split2 = ℚ ⊕ ℚ`: `e₀² = e₀`, `e₁² = e₁`, `e₀e₁ = 0` -/
namespace Split2

/-- structure constants -/
def T : Fin 2 → Fin 2 → (Fin 2 → ℚ) :=
  ![![![1, 0], ![0, 0]],
    ![![0, 0], ![0, 1]]]

/-- the product -/
def μ : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) := structProduct T

theorem mul_apply (u v : Fin 2 → ℚ) : μ u v = ![u 0 * v 0, u 1 * v 1] := by
  ext k
  fin_cases k <;> simp [μ, structProduct, T, Fin.sum_univ_two]

theorem e_ne : (e 0 : Fin 2 → ℚ) ≠ e 1 := by
  intro h
  have := congrFun h 0
  simp [e] at this

theorem not_mem0 : (e 1 : Fin 2 → ℚ) ∉ Submodule.span ℚ {e 0} := by
  rw [Submodule.mem_span_singleton]
  rintro ⟨t, ht⟩
  have := congrFun ht 1
  simp [e] at this

theorem not_mem1 : (e 0 : Fin 2 → ℚ) ∉ Submodule.span ℚ {e 1} := by
  rw [Submodule.mem_span_singleton]
  rintro ⟨t, ht⟩
  have := congrFun ht 0
  simp [e] at this

theorem ideal (i : Fin 2) : IsIdeal μ (Submodule.span ℚ {e i}) := by
  intro u v hv
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
  constructor
  · refine Submodule.mem_span_singleton.mpr ⟨u i * t, ?_⟩
    rw [mul_apply]
    ext k
    fin_cases i <;> fin_cases k <;> simp [e]
  · refine Submodule.mem_span_singleton.mpr ⟨u i * t, ?_⟩
    rw [mul_apply]
    ext k
    fin_cases i <;> fin_cases k <;> simp [e] <;> ring_nf

theorem span_top : Submodule.span ℚ {e 0} ⊔ Submodule.span ℚ {e 1} = (⊤ : Submodule ℚ (Fin 2 → ℚ)) := by
  rw [eq_top_iff]
  intro u _
  have hu : u = u 0 • e 0 + u 1 • e 1 := by
    ext k
    fin_cases k <;> simp [e]
  rw [hu]
  exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
    (Submodule.smul_mem _ _ (Submodule.subset_span rfl))

theorem ne_top (i : Fin 2) : Submodule.span ℚ {e i} ≠ (⊤ : Submodule ℚ (Fin 2 → ℚ)) := by
  intro h
  fin_cases i
  · exact not_mem0 (h ▸ Submodule.mem_top)
  · exact not_mem1 (h ▸ Submodule.mem_top)

/-- `ℚ ⊕ ℚ` is decomposable (sum of its proper ideals `⟨e₀⟩`, `⟨e₁⟩`). -/
example : IsDecomposable μ := by
  unfold IsDecomposable IsDecomposableSub
  apply le_antisymm le_top
  calc (⊤ : Submodule ℚ (Fin 2 → ℚ))
      = Submodule.span ℚ {e 0} ⊔ Submodule.span ℚ {e 1} := span_top.symm
    _ ≤ sSup {J : Submodule ℚ (Fin 2 → ℚ) | IsIdealIn μ ⊤ J ∧ J ≠ ⊤} :=
        sup_le (le_sSup ⟨⟨le_top, fun u _ v hv => ideal 0 u v hv⟩, ne_top 0⟩)
          (le_sSup ⟨⟨le_top, fun u _ v hv => ideal 1 u v hv⟩, ne_top 1⟩)

/-- `ℚ ⊕ ℚ` is not simple. -/
example : ¬ IsSimpleAlg μ := by
  rintro ⟨-, h⟩
  rcases h _ (ideal 0) with h0 | h0
  · have : (e 0 : Fin 2 → ℚ) ∈ Submodule.span ℚ {e 0} := Submodule.subset_span rfl
    rw [h0, Submodule.mem_bot] at this
    have := congrFun this 0
    simp [e] at this
  · exact ne_top 0 h0

/-- `ℚ ⊕ ℚ` has the non-trivial sum decomposition `{⟨e₀⟩, ⟨e₁⟩}`. -/
example : ¬ OnlyTrivialSumDecompositions μ := by
  intro h
  have hS : IsSumDecomposition μ {Submodule.span ℚ {e 0}, Submodule.span ℚ {e 1}} := by
    refine ⟨?_, ?_, ?_⟩
    · rintro B (rfl | rfl) u _ v hv
      · exact (ideal 0 u v hv).1
      · exact (ideal 1 u v hv).1
    · rintro B (rfl | rfl) C (rfl | rfl) hBC u hu v hv
      · exact absurd rfl hBC
      · obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
        rw [mul_apply]
        ext k
        fin_cases k <;> simp [e]
      · obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
        rw [mul_apply]
        ext k
        fin_cases k <;> simp [e]
      · exact absurd rfl hBC
    · rw [eq_top_iff, ← span_top]
      refine sup_le ?_ ?_ <;> rw [Submodule.span_le] <;> rintro _ rfl <;>
        refine Submodule.mem_sInf.mpr fun S hS => hS.1 ?_
      · exact Set.mem_biUnion (Set.mem_insert _ _) (Submodule.subset_span rfl)
      · exact Set.mem_biUnion (Set.mem_insert_of_mem _ rfl) (Submodule.subset_span rfl)
  rcases h _ hS with h0 | h0
  · exact ne_top 0 h0.symm
  · exact ne_top 1 (Set.mem_singleton_iff.mp h0).symm

/-- In `ℚ ⊕ ℚ` with `X = {e₀, e₁}`, the non-annihilation graph is not connected. -/
example : ¬ (nonAnnGraph μ {e 0, e 1}).Connected := by
  intro hc
  have hX0 : (e 0 : Fin 2 → ℚ) ∈ ({e 0, e 1} : Set (Fin 2 → ℚ)) := Set.mem_insert _ _
  have hX1 : (e 1 : Fin 2 → ℚ) ∈ ({e 0, e 1} : Set (Fin 2 → ℚ)) := Set.mem_insert_of_mem _ rfl
  have noAdj : ∀ p q : ({e 0, e 1} : Set (Fin 2 → ℚ)), ¬ (nonAnnGraph μ {e 0, e 1}).Adj p q := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ hadj
    rw [nonAnnGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨hne, hpq⟩ := hadj
    have hne' : p ≠ q := fun h => hne (Subtype.ext h)
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact hne' rfl
    · apply hpq.elim <;> intro h <;> apply h <;> rw [mul_apply] <;> ext k <;>
        fin_cases k <;> simp [e]
    · apply hpq.elim <;> intro h <;> apply h <;> rw [mul_apply] <;> ext k <;>
        fin_cases k <;> simp [e]
    · exact hne' rfl
  have key : ∀ {u v : ({e 0, e 1} : Set (Fin 2 → ℚ))},
      (nonAnnGraph μ {e 0, e 1}).Walk u v → u = v := by
    intro u v w
    cases w with
    | nil => rfl
    | cons h _ => exact (noAdj _ _ h).elim
  obtain ⟨w⟩ := hc.preconnected ⟨e 0, hX0⟩ ⟨e 1, hX1⟩
  exact e_ne (congrArg Subtype.val (key w))

end Split2

/-! ### `One = ℚ` with `e₀² = e₀` -/
namespace One

/-- structure constants -/
def T : Fin 1 → Fin 1 → (Fin 1 → ℚ) := ![![![1]]]

/-- the product -/
def μ : (Fin 1 → ℚ) →ₗ[ℚ] (Fin 1 → ℚ) →ₗ[ℚ] (Fin 1 → ℚ) := structProduct T

theorem eq_bot_or_top (J : Submodule ℚ (Fin 1 → ℚ)) : J = ⊥ ∨ J = ⊤ := by
  by_cases h : ∃ v ∈ J, v ≠ 0
  · right
    obtain ⟨v, hv, hv0⟩ := h
    have hv00 : v 0 ≠ 0 := by
      intro h0
      apply hv0
      ext k
      fin_cases k
      simpa using h0
    rw [eq_top_iff]
    intro u _
    have hu : u = (u 0 / v 0) • v := by
      ext k
      fin_cases k
      simp [div_mul_cancel₀ _ hv00]
    rw [hu]
    exact J.smul_mem _ hv
  · left
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hne
    exact h ⟨v, hv, hne⟩

theorem e0_ne : (e 0 : Fin 1 → ℚ) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [e] at this

/-- Deliberately false instance: `ℚ` is **not** decomposable. -/
example : ¬ IsDecomposable μ := by
  intro h
  unfold IsDecomposable IsDecomposableSub at h
  have hle : sSup {J : Submodule ℚ (Fin 1 → ℚ) | IsIdealIn μ ⊤ J ∧ J ≠ ⊤} ≤ ⊥ := by
    refine sSup_le fun J hJ => ?_
    rcases eq_bot_or_top J with hJ' | hJ'
    · exact hJ'.le
    · exact absurd hJ' hJ.2
  rw [h] at hle
  have : (e 0 : Fin 1 → ℚ) ∈ (⊥ : Submodule ℚ (Fin 1 → ℚ)) := hle Submodule.mem_top
  exact e0_ne ((Submodule.mem_bot ℚ).mp this)

/-- `ℚ` is simple. -/
example : IsSimpleAlg μ := by
  refine ⟨⟨e 0, e 0, ?_⟩, fun I _ => eq_bot_or_top I⟩
  intro h
  have := congrFun h 0
  simp [μ, structProduct, T, e] at this

end One

/-! ## 5. Version 1 (reviewed, SHA-256 `76caf8d5…0e5b`) versus version 2 (FIX-1)

The version-1 forms are restated verbatim here (namespace `V1`) so that the relation can be
checked: each fixed `∀`-statement is implied by its version-1 form (so its negation is at least as
strong), and the fixed existence statement implies its version-1 form. -/
namespace V1

/-- version 1 of `MS_Conjecture_3_16` -/
def MS_Conjecture_3_16 : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    IsPrimitiveAxialAlgebra F μ X → ComponentsAnnihilate μ X

/-- version 1 of `FinestSumDecomposition_connected` -/
def FinestSumDecomposition_connected : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    IsPrimitiveAxialAlgebra F μ X → OnlyTrivialSumDecompositions μ → (nonAnnGraph μ X).Connected

/-- version 1 of `Indecomposable_connected` -/
def Indecomposable_connected : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    IsPrimitiveAxialAlgebra F μ X → ¬ IsDecomposable μ → (nonAnnGraph μ X).Connected

/-- version 1 of `Simple_connected` -/
def Simple_connected : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    IsPrimitiveAxialAlgebra F μ X → IsSimpleAlg μ → (nonAnnGraph μ X).Connected

/-- version 1 of `Blocks_indecomposable` -/
def Blocks_indecomposable : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    IsPrimitiveAxialAlgebra F μ X → ∀ a ∈ X, ¬ IsDecomposableSub μ (block μ a)

/-- version 1 of `Dominance_nonsymmetric` -/
def Dominance_nonsymmetric : Prop :=
  ∃ (K : Type) (_ : Field K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    IsPrimitiveAxialAlgebra F μ X ∧ ∃ a ∈ X, ∃ b ∈ X, block μ a < block μ b

end V1

example (h : V1.MS_Conjecture_3_16) : MS_Conjecture_3_16 :=
  fun K _ V _ _ F μ X _ hA => h K V F μ X hA

example (h : V1.FinestSumDecomposition_connected) : FinestSumDecomposition_connected :=
  fun K _ V _ _ F μ X _ hA => h K V F μ X hA

example (h : V1.Indecomposable_connected) : Indecomposable_connected :=
  fun K _ V _ _ F μ X _ hA => h K V F μ X hA

example (h : V1.Simple_connected) : Simple_connected :=
  fun K _ V _ _ F μ X _ hA => h K V F μ X hA

example (h : V1.Blocks_indecomposable) : Blocks_indecomposable :=
  fun K _ V _ _ F μ X _ hA => h K V F μ X hA

example (h : Dominance_nonsymmetric) : V1.Dominance_nonsymmetric := by
  obtain ⟨K, i1, V, i2, i3, F, μ, X, _, hA, hb⟩ := h
  exact ⟨K, i1, V, i2, i3, F, μ, X, hA, hb⟩

#check @MS_Conjecture_3_16
#check @Corollary
#print axioms structProduct

end AxialMSZ.ChallengeTests
