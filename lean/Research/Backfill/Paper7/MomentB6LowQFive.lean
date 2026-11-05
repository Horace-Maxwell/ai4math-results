import Research.Backfill.Paper7.MomentB6LowQFour

/-! SOURCE ONLY. Universal target-five bounded-sum formula. The seven terms
are the seven partitions of five. Coefficients vanish before any potentially
invalid predecessor cancellation. Every support inequality is supplied inside
the final dimension induction; no positivity, sorting, graph or capacity-total
premise is added. DP2/DP3 have actual success records. The exact DP4 source is a
pending parent, not a compiled theorem here. No numerical/W6/transport source,
native computation, budget change or execution plan is included. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open Paper7MomentDP
open scoped BigOperators

def boundedQCapacityFiveExpr (a b c d e : ℕ) : ℕ :=
  a.choose 5 + b * (a - 1).choose 3 + b.choose 2 * (a - 2) +
    c * (a - 1).choose 2 + c * (b - 1) + d * (a - 1) + e
#print axioms Paper7MomentCounts.boundedQCapacityFiveExpr

theorem boundedQSupport_choose_three_pred_add (a b : ℕ) (hba : b ≤ a) :
    b * (a - 1).choose 3 + b * (a - 1).choose 2 = b * a.choose 3 := by
  cases a with
  | zero =>
    have hb : b = 0 := by omega
    simp [hb]
  | succ a =>
    rw [Nat.add_sub_cancel, Nat.choose_succ_succ' a 2]
    ring
#print axioms Paper7MomentCounts.boundedQSupport_choose_three_pred_add

theorem boundedQSupport_choose_two_sub_two_add (a b : ℕ) (hba : b ≤ a) :
    b.choose 2 * (a - 2) + b.choose 2 = b.choose 2 * (a - 1) := by
  by_cases hb : b < 2
  · have hzero : b.choose 2 = 0 := Nat.choose_eq_zero_of_lt hb
    simp [hzero]
  · have ha : 2 ≤ a := by omega
    have hsub : (a - 2) + 1 = a - 1 := by omega
    calc
      b.choose 2 * (a - 2) + b.choose 2 = b.choose 2 * ((a - 2) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = b.choose 2 * (a - 1) := by rw [hsub]
#print axioms Paper7MomentCounts.boundedQSupport_choose_two_sub_two_add

theorem boundedQCapacityFiveExpr_first (a b c d e : ℕ)
    (hba : b ≤ a) (hca : c ≤ a) (hda : d ≤ a) :
    boundedQCapacityFiveExpr (a + 1) b c d e =
      boundedQCapacityFiveExpr a b c d e + boundedQCapacityFourExpr a b c d := by
  unfold boundedQCapacityFiveExpr boundedQCapacityFourExpr
  have hsub : (a + 1) - 2 = a - 1 := by omega
  rw [Nat.add_sub_cancel, hsub, Nat.choose_succ_succ' a 4]
  rw [← boundedQSupport_choose_three_pred_add a b hba,
    ← boundedQSupport_choose_two_sub_two_add a b hba,
    ← boundedQSupport_choose_two_pred_add a c hca,
    ← boundedQSupport_pred_mul_add a d hda]
  norm_num only
  omega
#print axioms Paper7MomentCounts.boundedQCapacityFiveExpr_first

theorem boundedQCapacityFiveExpr_second (a b c d e : ℕ) (hcb : c ≤ b) :
    boundedQCapacityFiveExpr (a + 1) (b + 1) c d e =
      boundedQCapacityFiveExpr (a + 1) b c d e +
        (a.choose 3 + b * (a - 1) + c) := by
  unfold boundedQCapacityFiveExpr
  have hsub : (a + 1) - 2 = a - 1 := by omega
  rw [Nat.add_sub_cancel, hsub, Nat.choose_succ_succ' b 1, Nat.choose_one_right]
  simp only [Nat.add_sub_cancel]
  norm_num only
  rw [← boundedQSupport_pred_mul_add b c hcb]
  ring
#print axioms Paper7MomentCounts.boundedQCapacityFiveExpr_second

theorem boundedQCapacityFiveExpr_third (a b c d e : ℕ) :
    boundedQCapacityFiveExpr (a + 1) (b + 1) (c + 1) d e =
      boundedQCapacityFiveExpr (a + 1) (b + 1) c d e + (a.choose 2 + b) := by
  unfold boundedQCapacityFiveExpr
  simp only [Nat.add_sub_cancel]
  ring
#print axioms Paper7MomentCounts.boundedQCapacityFiveExpr_third

theorem boundedQCapacityFiveExpr_fourth (a b c d e : ℕ) :
    boundedQCapacityFiveExpr (a + 1) b c (d + 1) e =
      boundedQCapacityFiveExpr (a + 1) b c d e + a := by
  unfold boundedQCapacityFiveExpr
  simp only [Nat.add_sub_cancel]
  ring
#print axioms Paper7MomentCounts.boundedQCapacityFiveExpr_fourth

theorem boundedQCapacityFiveExpr_fifth (a b c d e : ℕ) :
    boundedQCapacityFiveExpr a b c d (e + 1) =
      boundedQCapacityFiveExpr a b c d e + 1 := by
  unfold boundedQCapacityFiveExpr
  ring
#print axioms Paper7MomentCounts.boundedQCapacityFiveExpr_fifth

theorem boundedQCapacityFiveExpr_capacity_update (a b c d e t : ℕ)
    (hba : b ≤ a) (hcb : c ≤ b) (hda : d ≤ a) :
    boundedQCapacityFiveExpr a b c d e +
      (if 1 ≤ t then boundedQCapacityFourExpr a b c d else 0) +
      (if 2 ≤ t then a.choose 3 + b * (a - 1) + c else 0) +
      (if 3 ≤ t then a.choose 2 + b else 0) +
      (if 4 ≤ t then a else 0) + (if 5 ≤ t then 1 else 0) =
      boundedQCapacityFiveExpr ((if 1 ≤ t then 1 else 0) + a)
        ((if 2 ≤ t then 1 else 0) + b) ((if 3 ≤ t then 1 else 0) + c)
        ((if 4 ≤ t then 1 else 0) + d) ((if 5 ≤ t then 1 else 0) + e) := by
  have hfirst := boundedQCapacityFiveExpr_first a b c d e hba (hcb.trans hba) hda
  have hsecond := boundedQCapacityFiveExpr_second a b c d e hcb
  have hthird := boundedQCapacityFiveExpr_third a b c d e
  have hfourth := boundedQCapacityFiveExpr_fourth a (b + 1) (c + 1) d e
  have hfifth := boundedQCapacityFiveExpr_fifth (a + 1) (b + 1) (c + 1) (d + 1) e
  have htwo : boundedQCapacityFiveExpr a b c d e + boundedQCapacityFourExpr a b c d +
      (a.choose 3 + b * (a - 1) + c) =
      boundedQCapacityFiveExpr (a + 1) (b + 1) c d e := by
    rw [← hfirst, ← hsecond]
  have hthree : boundedQCapacityFiveExpr a b c d e + boundedQCapacityFourExpr a b c d +
      (a.choose 3 + b * (a - 1) + c) + (a.choose 2 + b) =
      boundedQCapacityFiveExpr (a + 1) (b + 1) (c + 1) d e := by
    rw [htwo, ← hthird]
  have hfour : boundedQCapacityFiveExpr a b c d e + boundedQCapacityFourExpr a b c d +
      (a.choose 3 + b * (a - 1) + c) + (a.choose 2 + b) + a =
      boundedQCapacityFiveExpr (a + 1) (b + 1) (c + 1) (d + 1) e := by
    rw [hthree, ← hfourth]
  have hfive : boundedQCapacityFiveExpr a b c d e + boundedQCapacityFourExpr a b c d +
      (a.choose 3 + b * (a - 1) + c) + (a.choose 2 + b) + a + 1 =
      boundedQCapacityFiveExpr (a + 1) (b + 1) (c + 1) (d + 1) (e + 1) := by
    rw [hfour, ← hfifth]
  by_cases h1 : 1 ≤ t
  · by_cases h2 : 2 ≤ t
    · by_cases h3 : 3 ≤ t
      · by_cases h4 : 4 ≤ t
        · by_cases h5 : 5 ≤ t
          · simpa [h1, h2, h3, h4, h5, Nat.add_comm] using hfive
          · simpa [h1, h2, h3, h4, h5, Nat.add_comm] using hfour
        · have h5 : ¬ 5 ≤ t := by omega
          simpa [h1, h2, h3, h4, h5, Nat.add_comm] using hthree
      · have h4 : ¬ 4 ≤ t := by omega
        have h5 : ¬ 5 ≤ t := by omega
        simpa [h1, h2, h3, h4, h5, Nat.add_comm] using htwo
    · have h3 : ¬ 3 ≤ t := by omega
      have h4 : ¬ 4 ≤ t := by omega
      have h5 : ¬ 5 ≤ t := by omega
      simpa [h1, h2, h3, h4, h5, Nat.add_comm] using hfirst.symm
  · have h2 : ¬ 2 ≤ t := by omega
    have h3 : ¬ 3 ≤ t := by omega
    have h4 : ¬ 4 ≤ t := by omega
    have h5 : ¬ 5 ≤ t := by omega
    simp [h1, h2, h3, h4, h5]
#print axioms Paper7MomentCounts.boundedQCapacityFiveExpr_capacity_update

theorem boundedQDP_head_five (n : ℕ) (z : Fin (n + 1) → ℕ) :
    boundedQDP (n + 1) z 5 = boundedQDP n (Fin.tail z) 5 +
      (if 1 ≤ z 0 then boundedQDP n (Fin.tail z) 4 else 0) +
      (if 2 ≤ z 0 then boundedQDP n (Fin.tail z) 3 else 0) +
      (if 3 ≤ z 0 then boundedQDP n (Fin.tail z) 2 else 0) +
      (if 4 ≤ z 0 then boundedQDP n (Fin.tail z) 1 else 0) +
      (if 5 ≤ z 0 then boundedQDP n (Fin.tail z) 0 else 0) := by
  rw [boundedQDP_head_truncated]
  norm_num [Fin.sum_univ_succ, Nat.add_assoc]
  simp only [Nat.succ_le_iff]
#print axioms Paper7MomentCounts.boundedQDP_head_five

theorem boundedQDP_five_eq_capacitySupports (n : ℕ) (z : Fin n → ℕ) :
    boundedQDP n z 5 = (boundedQCapacitySupport n z 1).choose 5 +
      boundedQCapacitySupport n z 2 * (boundedQCapacitySupport n z 1 - 1).choose 3 +
      (boundedQCapacitySupport n z 2).choose 2 * (boundedQCapacitySupport n z 1 - 2) +
      boundedQCapacitySupport n z 3 * (boundedQCapacitySupport n z 1 - 1).choose 2 +
      boundedQCapacitySupport n z 3 * (boundedQCapacitySupport n z 2 - 1) +
      boundedQCapacitySupport n z 4 * (boundedQCapacitySupport n z 1 - 1) +
      boundedQCapacitySupport n z 5 := by
  change boundedQDP n z 5 = boundedQCapacityFiveExpr
    (boundedQCapacitySupport n z 1) (boundedQCapacitySupport n z 2)
    (boundedQCapacitySupport n z 3) (boundedQCapacitySupport n z 4)
    (boundedQCapacitySupport n z 5)
  induction n with
  | zero => simp [boundedQDP_zero, boundedQCapacitySupport, boundedQCapacityFiveExpr]
  | succ n ih =>
    rw [boundedQDP_head_five, ih, boundedQDP_four_eq_capacitySupports,
      boundedQDP_three_eq_capacitySupports, boundedQDP_two_eq_capacitySupports,
      boundedQDP_one_eq_capacitySupport, boundedQDP_zero_capacity_eq_one,
      boundedQCapacitySupport_head n z 1, boundedQCapacitySupport_head n z 2,
      boundedQCapacitySupport_head n z 3, boundedQCapacitySupport_head n z 4,
      boundedQCapacitySupport_head n z 5]
    exact boundedQCapacityFiveExpr_capacity_update _ _ _ _ _ (z 0)
      (boundedQCapacitySupport_mono n (Fin.tail z) 1 2 (by omega))
      (boundedQCapacitySupport_mono n (Fin.tail z) 2 3 (by omega))
      (boundedQCapacitySupport_mono n (Fin.tail z) 1 4 (by omega))
#print axioms Paper7MomentCounts.boundedQDP_five_eq_capacitySupports

end Paper7MomentCounts
