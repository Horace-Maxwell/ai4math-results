import Research.Backfill.Paper7.MomentB6LowQThree

/-! SOURCE ONLY. Generic target-four bounded-sum formula. The existing head
recurrence and support nesting supply every premise of the arithmetic helpers.
Zero dimensions and zero/one capacities remain in the final theorem. This is
not a numerical slice, graph hypothesis, budget change or execution plan. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open Paper7MomentDP
open scoped BigOperators

def boundedQCapacityFourExpr (a b c d : ℕ) : ℕ :=
  a.choose 4 + b * (a - 1).choose 2 + b.choose 2 + c * (a - 1) + d
#print axioms Paper7MomentCounts.boundedQCapacityFourExpr

theorem boundedQSupport_choose_two_pred_add (a b : ℕ) (hba : b ≤ a) :
    b * (a - 1).choose 2 + b * (a - 1) = b * a.choose 2 := by
  cases a with
  | zero =>
    have hb : b = 0 := by omega
    simp [hb]
  | succ a =>
    rw [Nat.add_sub_cancel, Nat.choose_succ_succ']
    simp only [Nat.choose_one_right]
    ring
#print axioms Paper7MomentCounts.boundedQSupport_choose_two_pred_add

theorem boundedQCapacityFourExpr_first (a b c d : ℕ)
    (hba : b ≤ a) (hca : c ≤ a) :
    boundedQCapacityFourExpr (a + 1) b c d =
      boundedQCapacityFourExpr a b c d + (a.choose 3 + b * (a - 1) + c) := by
  unfold boundedQCapacityFourExpr
  rw [Nat.add_sub_cancel, Nat.choose_succ_succ']
  rw [← boundedQSupport_choose_two_pred_add a b hba,
    ← boundedQSupport_pred_mul_add a c hca]
  norm_num only
  omega
#print axioms Paper7MomentCounts.boundedQCapacityFourExpr_first

theorem boundedQCapacityFourExpr_second (a b c d : ℕ) :
    boundedQCapacityFourExpr (a + 1) (b + 1) c d =
      boundedQCapacityFourExpr (a + 1) b c d + (a.choose 2 + b) := by
  unfold boundedQCapacityFourExpr
  simp only [Nat.add_sub_cancel, Nat.choose_succ_succ' b 1, Nat.choose_one_right]
  ring
#print axioms Paper7MomentCounts.boundedQCapacityFourExpr_second

theorem boundedQCapacityFourExpr_third (a b c d : ℕ) :
    boundedQCapacityFourExpr (a + 1) b (c + 1) d =
      boundedQCapacityFourExpr (a + 1) b c d + a := by
  unfold boundedQCapacityFourExpr
  simp only [Nat.add_sub_cancel]
  ring
#print axioms Paper7MomentCounts.boundedQCapacityFourExpr_third

theorem boundedQCapacityFourExpr_fourth (a b c d : ℕ) :
    boundedQCapacityFourExpr a b c (d + 1) =
      boundedQCapacityFourExpr a b c d + 1 := by
  unfold boundedQCapacityFourExpr
  ring
#print axioms Paper7MomentCounts.boundedQCapacityFourExpr_fourth

theorem boundedQCapacityFourExpr_capacity_update (a b c d t : ℕ)
    (hba : b ≤ a) (hca : c ≤ a) :
    boundedQCapacityFourExpr a b c d +
      (if 1 ≤ t then a.choose 3 + b * (a - 1) + c else 0) +
      (if 2 ≤ t then a.choose 2 + b else 0) +
      (if 3 ≤ t then a else 0) + (if 4 ≤ t then 1 else 0) =
      boundedQCapacityFourExpr ((if 1 ≤ t then 1 else 0) + a)
        ((if 2 ≤ t then 1 else 0) + b) ((if 3 ≤ t then 1 else 0) + c)
        ((if 4 ≤ t then 1 else 0) + d) := by
  have hfirst := boundedQCapacityFourExpr_first a b c d hba hca
  have hsecond := boundedQCapacityFourExpr_second a b c d
  have hthird := boundedQCapacityFourExpr_third a (b + 1) c d
  have hfourth := boundedQCapacityFourExpr_fourth (a + 1) (b + 1) (c + 1) d
  have htwo : boundedQCapacityFourExpr a b c d +
      (a.choose 3 + b * (a - 1) + c) + (a.choose 2 + b) =
      boundedQCapacityFourExpr (a + 1) (b + 1) c d := by
    rw [← hfirst, ← hsecond]
  have hthree : boundedQCapacityFourExpr a b c d +
      (a.choose 3 + b * (a - 1) + c) + (a.choose 2 + b) + a =
      boundedQCapacityFourExpr (a + 1) (b + 1) (c + 1) d := by
    rw [htwo, ← hthird]
  have hfour : boundedQCapacityFourExpr a b c d +
      (a.choose 3 + b * (a - 1) + c) + (a.choose 2 + b) + a + 1 =
      boundedQCapacityFourExpr (a + 1) (b + 1) (c + 1) (d + 1) := by
    rw [hthree, ← hfourth]
  by_cases h1 : 1 ≤ t
  · by_cases h2 : 2 ≤ t
    · by_cases h3 : 3 ≤ t
      · by_cases h4 : 4 ≤ t
        · simpa [h1, h2, h3, h4, Nat.add_comm] using hfour
        · simpa [h1, h2, h3, h4, Nat.add_comm] using hthree
      · have h4 : ¬ 4 ≤ t := by omega
        simpa [h1, h2, h3, h4, Nat.add_comm] using htwo
    · have h3 : ¬ 3 ≤ t := by omega
      have h4 : ¬ 4 ≤ t := by omega
      simpa [h1, h2, h3, h4, Nat.add_comm] using hfirst.symm
  · have h2 : ¬ 2 ≤ t := by omega
    have h3 : ¬ 3 ≤ t := by omega
    have h4 : ¬ 4 ≤ t := by omega
    simp [h1, h2, h3, h4]
#print axioms Paper7MomentCounts.boundedQCapacityFourExpr_capacity_update

theorem boundedQDP_head_four (n : ℕ) (z : Fin (n + 1) → ℕ) :
    boundedQDP (n + 1) z 4 = boundedQDP n (Fin.tail z) 4 +
      (if 1 ≤ z 0 then boundedQDP n (Fin.tail z) 3 else 0) +
      (if 2 ≤ z 0 then boundedQDP n (Fin.tail z) 2 else 0) +
      (if 3 ≤ z 0 then boundedQDP n (Fin.tail z) 1 else 0) +
      (if 4 ≤ z 0 then boundedQDP n (Fin.tail z) 0 else 0) := by
  rw [boundedQDP_head_truncated]
  norm_num [Fin.sum_univ_succ, Nat.add_assoc]
  simp only [Nat.succ_le_iff]
#print axioms Paper7MomentCounts.boundedQDP_head_four

theorem boundedQDP_four_eq_capacitySupports (n : ℕ) (z : Fin n → ℕ) :
    boundedQDP n z 4 = (boundedQCapacitySupport n z 1).choose 4 +
      boundedQCapacitySupport n z 2 * (boundedQCapacitySupport n z 1 - 1).choose 2 +
      (boundedQCapacitySupport n z 2).choose 2 +
      boundedQCapacitySupport n z 3 * (boundedQCapacitySupport n z 1 - 1) +
      boundedQCapacitySupport n z 4 := by
  change boundedQDP n z 4 = boundedQCapacityFourExpr
    (boundedQCapacitySupport n z 1) (boundedQCapacitySupport n z 2)
    (boundedQCapacitySupport n z 3) (boundedQCapacitySupport n z 4)
  induction n with
  | zero => simp [boundedQDP_zero, boundedQCapacitySupport, boundedQCapacityFourExpr]
  | succ n ih =>
    rw [boundedQDP_head_four, ih, boundedQDP_three_eq_capacitySupports,
      boundedQDP_two_eq_capacitySupports, boundedQDP_one_eq_capacitySupport,
      boundedQDP_zero_capacity_eq_one,
      boundedQCapacitySupport_head n z 1, boundedQCapacitySupport_head n z 2,
      boundedQCapacitySupport_head n z 3, boundedQCapacitySupport_head n z 4]
    exact boundedQCapacityFourExpr_capacity_update _ _ _ _ (z 0)
      (boundedQCapacitySupport_mono n (Fin.tail z) 1 2 (by omega))
      (boundedQCapacitySupport_mono n (Fin.tail z) 1 3 (by omega))
#print axioms Paper7MomentCounts.boundedQDP_four_eq_capacitySupports

end Paper7MomentCounts
