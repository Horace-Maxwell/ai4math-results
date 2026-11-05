import Research.Backfill.Paper7.MomentB6SevenSupport

/-! Source-only candidate. Genuine original bounded-q fibres are shown to be
singletons; no evaluated DP table or assumed block weight is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators

theorem boundedQDP_full_capacity_eq_one (n : ℕ) (z : Fin n → ℕ) :
    Paper7MomentDP.boundedQDP n z (∑ i, z i) = 1 := by
  rw [Paper7MomentDP.boundedQDP_eq_fibre_card]
  let qmax : (i : Fin n) → Fin (z i + 1) := fun i => ⟨z i,Nat.lt_succ_self _⟩
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨qmax,rfl⟩,?_⟩
  intro q
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hle : ∀ j ∈ (Finset.univ : Finset (Fin n)), (q.val j).val ≤ z j :=
    fun j _ => Nat.le_of_lt_succ (q.val j).isLt
  have he := (Finset.sum_eq_sum_iff_of_le hle).mp q.property
  exact he i (Finset.mem_univ i)
#print axioms Paper7MomentCounts.boundedQDP_full_capacity_eq_one

theorem b6_boundedQDP_single_eq_one (i : Fin 6) (Q : ℕ) (hQ : Q ≤ 7) :
    Paper7MomentDP.boundedQDP 6 (b6SevenSingle i) Q = 1 := by
  rw [Paper7MomentDP.boundedQDP_eq_fibre_card]
  let q0 : (k : Fin 6) → Fin (b6SevenSingle i k + 1) := fun k =>
    ⟨if k = i then Q else 0,by
      by_cases hk : k = i
      · subst k
        simpa [b6SevenSingle] using Nat.lt_succ_of_le hQ
      · simp [b6SevenSingle,hk]⟩
  have hsum : (∑ k, (q0 k).val) = Q := by simp [q0]
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨q0,hsum⟩,?_⟩
  intro q
  have hout (k : Fin 6) (hk : k ≠ i) : (q.val k).val = 0 := by
    have hb := (q.val k).isLt
    simp only [b6SevenSingle,ite_eq_right hk] at hb
    omega
  have hi : (q.val i).val = Q := by
    have hs : (∑ k, (q.val k).val) = (q.val i).val := by
      apply Finset.sum_eq_single i
      · intro k _hk hki
        exact hout k hki
      · intro hni
        exact False.elim (hni (Finset.mem_univ i))
    exact hs.symm.trans q.property
  apply Subtype.ext
  funext k
  apply Fin.ext
  by_cases hk : k = i
  · subst k
    simpa [q0] using hi
  · simp [q0,hk,hout k hk]
#print axioms Paper7MomentCounts.b6_boundedQDP_single_eq_one

theorem b6_seven_shapes_weight_one (z : Fin 6 → ℕ) (Q : ℕ)
    (hs : B6SevenShapes z Q) : Paper7MomentDP.boundedQDP 6 z Q = 1 := by
  rcases hs with ⟨i,rfl,hQ⟩ | ⟨i,j,hij,rfl,rfl⟩
  · apply b6_boundedQDP_single_eq_one
    rcases hQ with rfl | rfl <;> decide
  · rw [← b6SevenDouble_sum i j hij]
    exact boundedQDP_full_capacity_eq_one 6 (b6SevenDouble i j)
#print axioms Paper7MomentCounts.b6_seven_shapes_weight_one

end Paper7MomentCounts
