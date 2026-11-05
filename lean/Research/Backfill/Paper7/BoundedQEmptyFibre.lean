import Research.Backfill.Paper7.BoundedQSumDP

/-! An empty-fibre lemma for the original bounded-q recurrence. No table is
evaluated and no spectral-feature witness contributes to this cardinality. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentDP
open scoped BigOperators Classical

theorem boundedQSum_le_total {n : ℕ} (z : Fin n → ℕ)
    (q : BoundedQAssignment z) : boundedQSum z q ≤ ∑ i, z i := by
  apply Finset.sum_le_sum
  intro i _
  exact Nat.le_of_lt_succ (q i).isLt
#print axioms Paper7MomentDP.boundedQSum_le_total

theorem boundedQFibre_isEmpty_of_total_lt {n : ℕ} (z : Fin n → ℕ) (Q : ℕ)
    (hQ : (∑ i, z i) < Q) : IsEmpty (BoundedQFibre z Q) := by
  refine ⟨fun q => ?_⟩
  have h := boundedQSum_le_total z q.val
  rw [q.property] at h
  exact (Nat.not_le_of_lt hQ) h
#print axioms Paper7MomentDP.boundedQFibre_isEmpty_of_total_lt

theorem boundedQDP_eq_zero_of_total_lt {n : ℕ} (z : Fin n → ℕ) (Q : ℕ)
    (hQ : (∑ i, z i) < Q) : boundedQDP n z Q = 0 := by
  let : IsEmpty (BoundedQFibre z Q) := boundedQFibre_isEmpty_of_total_lt z Q hQ
  rw [boundedQDP_eq_card]
  exact Nat.card_of_isEmpty
#print axioms Paper7MomentDP.boundedQDP_eq_zero_of_total_lt

end Paper7MomentDP
