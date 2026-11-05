import Research.Backfill.Paper7.MomentB6LowQTwo

/-! SOURCE ONLY. Generic target-three bounded-sum formula, using the separate
target-two module. Support nesting supplies every natural-subtraction premise.
No original graph hypothesis, sortedness, positive capacity or total-capacity
bound is assumed. This is not a numerical Q-slice or a candidate execution. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open Paper7MomentDP
open scoped BigOperators

theorem boundedQDP_head_three (n : ℕ) (z : Fin (n + 1) → ℕ) :
    boundedQDP (n + 1) z 3 = boundedQDP n (Fin.tail z) 3 +
      (if 1 ≤ z 0 then boundedQDP n (Fin.tail z) 2 else 0) +
      (if 2 ≤ z 0 then boundedQDP n (Fin.tail z) 1 else 0) +
      (if 3 ≤ z 0 then boundedQDP n (Fin.tail z) 0 else 0) := by
  rw [boundedQDP_head_truncated]
  norm_num [Fin.sum_univ_succ, Nat.add_assoc]
  simp only [Nat.succ_le_iff]
#print axioms Paper7MomentCounts.boundedQDP_head_three

theorem boundedQSupport_pred_mul_add (a b : ℕ) (hba : b ≤ a) :
    b * (a - 1) + b = b * a := by
  by_cases ha : a = 0
  · have hb : b = 0 := by omega
    simp [ha, hb]
  · have ha1 : 1 ≤ a := by omega
    calc
      b * (a - 1) + b = b * ((a - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = b * a := by rw [Nat.sub_add_cancel ha1]
#print axioms Paper7MomentCounts.boundedQSupport_pred_mul_add

theorem boundedQDP_three_eq_capacitySupports (n : ℕ) (z : Fin n → ℕ) :
    boundedQDP n z 3 = (boundedQCapacitySupport n z 1).choose 3 +
      boundedQCapacitySupport n z 2 * (boundedQCapacitySupport n z 1 - 1) +
      boundedQCapacitySupport n z 3 := by
  induction n with
  | zero => simp [boundedQDP_zero, boundedQCapacitySupport]
  | succ n ih =>
    rw [boundedQDP_head_three, ih, boundedQDP_two_eq_capacitySupports,
      boundedQDP_one_eq_capacitySupport, boundedQDP_zero_capacity_eq_one,
      boundedQCapacitySupport_head n z 1, boundedQCapacitySupport_head n z 2,
      boundedQCapacitySupport_head n z 3]
    by_cases h1 : 1 ≤ z 0
    · simp only [h1, ite_true]
      have hc : (1 + boundedQCapacitySupport n (Fin.tail z) 1).choose 3 =
          (boundedQCapacitySupport n (Fin.tail z) 1).choose 2 +
            (boundedQCapacitySupport n (Fin.tail z) 1).choose 3 := by
        simpa only [Nat.add_comm 1 (boundedQCapacitySupport n (Fin.tail z) 1)] using
          (Nat.choose_succ_succ' (boundedQCapacitySupport n (Fin.tail z) 1) 2)
      have hs : boundedQCapacitySupport n (Fin.tail z) 2 *
          (boundedQCapacitySupport n (Fin.tail z) 1 - 1) +
          boundedQCapacitySupport n (Fin.tail z) 2 =
          boundedQCapacitySupport n (Fin.tail z) 2 *
            boundedQCapacitySupport n (Fin.tail z) 1 :=
        boundedQSupport_pred_mul_add _ _
          (boundedQCapacitySupport_mono n (Fin.tail z) 1 2 (by omega))
      rw [hc, Nat.add_sub_cancel_left, Nat.add_mul, ← hs]
      by_cases h2 : 2 ≤ z 0 <;>
        simp only [h2, ite_true, ite_false, Nat.one_mul, Nat.zero_mul] <;> omega
    · have h2 : ¬ 2 ≤ z 0 := by omega
      have h3 : ¬ 3 ≤ z 0 := by omega
      simp [h1, h2, h3]
#print axioms Paper7MomentCounts.boundedQDP_three_eq_capacitySupports

end Paper7MomentCounts
