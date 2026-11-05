import Research.Backfill.Paper7.IntroPrincipalGapBudget

/-! Exact factorization across an actual separated vertex partition. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroCutGap
open Matrix Polynomial BackfillPaper7.Challenge

theorem separated_partition_charpoly
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ¬G.Adj i j) :
    (G.adjMatrix ℝ).charpoly =
      ((G.induce S).adjMatrix ℝ).charpoly * ((G.induce (Sᶜ)).adjMatrix ℝ).charpoly := by
  let e : S ⊕ (Sᶜ : Set V) ≃ V := Equiv.Set.sumCompl S
  have hblock : Matrix.reindex e.symm e.symm (G.adjMatrix ℝ) =
      Matrix.fromBlocks ((G.induce S).adjMatrix ℝ) 0 0 ((G.induce (Sᶜ)).adjMatrix ℝ) := by
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · change (if G.Adj i.val j.val then (1 : ℝ) else 0) = 0
      rw [ite_eq_right (hsep i.val i.property j.val j.property)]
    · change (if G.Adj i.val j.val then (1 : ℝ) else 0) = 0
      have hn : ¬G.Adj i.val j.val := fun h => hsep j.val j.property i.val i.property h.symm
      rw [ite_eq_right hn]
    · rfl
  calc
    _ = (Matrix.reindex e.symm e.symm (G.adjMatrix ℝ)).charpoly :=
      (Matrix.charpoly_reindex e.symm (G.adjMatrix ℝ)).symm
    _ = _ := by rw [hblock, Matrix.charpoly_fromBlocks_zero₁₂]
#print axioms Paper7IntroCutGap.separated_partition_charpoly

theorem separated_partition_spec
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ¬G.Adj i j) :
    spec G = spec (G.induce S) + spec (G.induce (Sᶜ)) := by
  change (G.adjMatrix ℝ).charpoly.roots =
    ((G.induce S).adjMatrix ℝ).charpoly.roots + ((G.induce (Sᶜ)).adjMatrix ℝ).charpoly.roots
  rw [separated_partition_charpoly G S hsep]
  exact Polynomial.roots_mul (mul_ne_zero ((G.induce S).adjMatrix ℝ).charpoly_monic.ne_zero
    ((G.induce (Sᶜ)).adjMatrix ℝ).charpoly_monic.ne_zero)
#print axioms Paper7IntroCutGap.separated_partition_spec

theorem separated_partition_open_gap
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V)
    (hsep : ∀ i ∈ S, ∀ j ∉ S, ¬G.Adj i j) (a b : ℝ) :
    openGapCount G a b = openGapCount (G.induce S) a b + openGapCount (G.induce (Sᶜ)) a b := by
  unfold openGapCount
  rw [separated_partition_spec G S hsep, Multiset.filter_add, Multiset.card_add]
#print axioms Paper7IntroCutGap.separated_partition_open_gap

end Paper7IntroCutGap
