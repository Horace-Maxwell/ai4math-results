import Research.Backfill.Paper7.MomentB6EndpointWeights

/-! SOURCE ONLY. Generic bounded-sum fibres at target two.
All dimensions and natural capacities, including zero capacities, remain.
The existing head recurrence is reindexed to the fixed target bound by an
explicit finite-set bijection. No capacity vector or target count is sampled.
No original graph condition, computation budget or numerical slice is added. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open Paper7MomentDP
open scoped BigOperators

def boundedQCapacitySupport (n : ℕ) (z : Fin n → ℕ) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => k ≤ z i)).card
#print axioms Paper7MomentCounts.boundedQCapacitySupport

theorem boundedQCapacitySupport_head (n : ℕ) (z : Fin (n + 1) → ℕ) (k : ℕ) :
    boundedQCapacitySupport (n + 1) z k =
      (if k ≤ z 0 then 1 else 0) + boundedQCapacitySupport n (Fin.tail z) k := by
  unfold boundedQCapacitySupport
  exact Fin.card_filter_univ_succ' (fun i : Fin (n + 1) => k ≤ z i)
#print axioms Paper7MomentCounts.boundedQCapacitySupport_head

theorem boundedQCapacitySupport_mono (n : ℕ) (z : Fin n → ℕ) (j k : ℕ)
    (hjk : j ≤ k) :
    boundedQCapacitySupport n z k ≤ boundedQCapacitySupport n z j := by
  unfold boundedQCapacitySupport
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hi).1, hjk.trans (Finset.mem_filter.mp hi).2⟩
#print axioms Paper7MomentCounts.boundedQCapacitySupport_mono

theorem boundedQCapacitySupport_one_eq_card (n : ℕ) (z : Fin n → ℕ) :
    boundedQCapacitySupport n z 1 = Nat.card {i : Fin n // 0 < z i} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [boundedQCapacitySupport, Nat.succ_le_iff]
#print axioms Paper7MomentCounts.boundedQCapacitySupport_one_eq_card

theorem boundedQDP_one_eq_capacitySupport (n : ℕ) (z : Fin n → ℕ) :
    boundedQDP n z 1 = boundedQCapacitySupport n z 1 :=
  (boundedQDP_one_eq_positive_support_card n z).trans
    (boundedQCapacitySupport_one_eq_card n z).symm
#print axioms Paper7MomentCounts.boundedQDP_one_eq_capacitySupport

theorem boundedQLowHeadSum_swap (c Q : ℕ) (f : ℕ → ℕ) :
    (∑ a : Fin (c + 1), if a.val ≤ Q then f (Q - a.val) else 0) =
      ∑ b : Fin (Q + 1), if b.val ≤ c then f (Q - b.val) else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij
    (fun a ha => (⟨a.val, by
      have h := (Finset.mem_filter.mp ha).2
      omega⟩ : Fin (Q + 1))) ?_ ?_ ?_ ?_
  · intro a _ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change a.val ≤ c
    have h := a.isLt
    omega
  · intro a ha b hb hab
    apply Fin.ext
    exact congrArg (fun t : Fin (Q + 1) => t.val) hab
  · intro b hb
    have hbc : b.val ≤ c := (Finset.mem_filter.mp hb).2
    let a : Fin (c + 1) := ⟨b.val, by omega⟩
    have ha : a ∈ Finset.univ.filter (fun t : Fin (c + 1) => t.val ≤ Q) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change b.val ≤ Q
      have h := b.isLt
      omega
    refine ⟨a, ha, ?_⟩
    apply Fin.ext
    rfl
  · intro a _ha
    rfl
#print axioms Paper7MomentCounts.boundedQLowHeadSum_swap

theorem boundedQDP_head_truncated (n : ℕ) (z : Fin (n + 1) → ℕ) (Q : ℕ) :
    boundedQDP (n + 1) z Q =
      ∑ a : Fin (Q + 1),
        if a.val ≤ z 0 then boundedQDP n (Fin.tail z) (Q - a.val) else 0 := by
  rw [boundedQDP_head]
  exact boundedQLowHeadSum_swap (z 0) Q (fun r => boundedQDP n (Fin.tail z) r)
#print axioms Paper7MomentCounts.boundedQDP_head_truncated

theorem boundedQDP_head_two (n : ℕ) (z : Fin (n + 1) → ℕ) :
    boundedQDP (n + 1) z 2 = boundedQDP n (Fin.tail z) 2 +
      (if 1 ≤ z 0 then boundedQDP n (Fin.tail z) 1 else 0) +
      (if 2 ≤ z 0 then boundedQDP n (Fin.tail z) 0 else 0) := by
  rw [boundedQDP_head_truncated]
  norm_num [Fin.sum_univ_succ, Nat.add_assoc]
  simp only [Nat.succ_le_iff]
#print axioms Paper7MomentCounts.boundedQDP_head_two

theorem boundedQDP_two_eq_capacitySupports (n : ℕ) (z : Fin n → ℕ) :
    boundedQDP n z 2 = (boundedQCapacitySupport n z 1).choose 2 +
      boundedQCapacitySupport n z 2 := by
  induction n with
  | zero => simp [boundedQDP_zero, boundedQCapacitySupport]
  | succ n ih =>
    rw [boundedQDP_head_two, ih, boundedQDP_one_eq_capacitySupport,
      boundedQDP_zero_capacity_eq_one,
      boundedQCapacitySupport_head n z 1, boundedQCapacitySupport_head n z 2]
    by_cases h1 : 1 ≤ z 0
    · simp only [h1, ite_true]
      have hc : (1 + boundedQCapacitySupport n (Fin.tail z) 1).choose 2 =
          boundedQCapacitySupport n (Fin.tail z) 1 +
            (boundedQCapacitySupport n (Fin.tail z) 1).choose 2 := by
        simpa only [Nat.add_comm 1 (boundedQCapacitySupport n (Fin.tail z) 1),
          Nat.choose_one_right] using
          (Nat.choose_succ_succ' (boundedQCapacitySupport n (Fin.tail z) 1) 1)
      rw [hc]
      omega
    · have h2 : ¬ 2 ≤ z 0 := by omega
      simp [h1, h2]
#print axioms Paper7MomentCounts.boundedQDP_two_eq_capacitySupports

end Paper7MomentCounts
