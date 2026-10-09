import Research.Backfill.Paper6.ChallengeV3
import Research.Backfill.Paper6.CalibBasic

/-!
# The same three coordinate-flat indicators as the frozen RemD162 statement

Candidate proof source, not yet compiled or accepted. The polynomial witness is
the sum of three products of six affine coordinate factors. The weight bridge
evaluates this exact indicator sum; no unrelated existential calibration witness
is substituted for it.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Remark162

open Finset
open BackfillPaper6.V3

def J1 : Finset ℕ := {1, 2, 3, 4, 5, 6}
def J2 : Finset ℕ := {7, 8, 9, 10, 11, 12}
def J3 : Finset ℕ := {1, 2, 3, 7, 8, 9}

def outside (J : Finset ℕ) : Finset (Fin 12) :=
  Finset.univ.filter (fun i => i.val + 1 ∉ J)

noncomputable def flatPolynomial (J : Finset ℕ) : MvPolynomial (Fin 12) (ZMod 2) :=
  ∏ i ∈ outside J, (1 + MvPolynomial.X i)

noncomputable def targetFunction : BFun 12 :=
  ind (coordSpan J1) + ind (coordSpan J2) + ind (coordSpan J3)

noncomputable def targetPolynomial : MvPolynomial (Fin 12) (ZMod 2) :=
  flatPolynomial J1 + flatPolynomial J2 + flatPolynomial J3

/-- A product of the missing-coordinate factors is exactly the flat indicator. -/
theorem eval_flatPolynomial (J : Finset ℕ) (x : Pt 12) :
    evalFun (flatPolynomial J) x = ind (coordSpan J) x := by
  classical
  have heval : evalFun (flatPolynomial J) x = ∏ i ∈ outside J, (1 + x i) := by
    simp only [evalFun, flatPolynomial, MvPolynomial.eval_prod,
      map_add, map_one, MvPolynomial.eval_X]
  rw [heval]
  by_cases hx : x ∈ coordSpan J
  · rw [show ind (coordSpan J) x = 1 by simp [ind, hx]]
    apply Finset.prod_eq_one
    intro i hi
    have hiJ : i.val + 1 ∉ J := (Finset.mem_filter.mp hi).2
    have hxi : x i = 0 := hx i hiJ
    rw [hxi]
    exact add_zero 1
  · rw [show ind (coordSpan J) x = 0 by simp [ind, hx]]
    have hex : ∃ i : Fin 12, i.val + 1 ∉ J ∧ x i ≠ 0 := by
      by_contra hnone
      apply hx
      intro i hiJ
      by_contra hxi
      exact hnone ⟨i, hiJ, hxi⟩
    obtain ⟨i, hiJ, hxi⟩ := hex
    apply Finset.prod_eq_zero (i := i)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hiJ⟩
    · have hz : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
      rw [hz (x i) hxi]
      decide

/-- Each missing-coordinate factor contributes degree at most one. -/
theorem flatPolynomial_degree_le (J : Finset ℕ) :
    (flatPolynomial J).totalDegree ≤ (outside J).card := by
  classical
  calc
    (flatPolynomial J).totalDegree ≤
        ∑ i ∈ outside J, (1 + (MvPolynomial.X i :
          MvPolynomial (Fin 12) (ZMod 2))).totalDegree :=
      MvPolynomial.totalDegree_finsetProd (outside J) (fun i => 1 + MvPolynomial.X i)
    _ ≤ ∑ _i ∈ outside J, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
    _ = (outside J).card := by simp

theorem targetPolynomial_degree : targetPolynomial.totalDegree ≤ 6 := by
  have hc1 : (outside J1).card = 6 := by decide +kernel
  have hc2 : (outside J2).card = 6 := by decide +kernel
  have hc3 : (outside J3).card = 6 := by decide +kernel
  have hd1 : (flatPolynomial J1).totalDegree ≤ 6 := by
    simpa only [hc1] using flatPolynomial_degree_le J1
  have hd2 : (flatPolynomial J2).totalDegree ≤ 6 := by
    simpa only [hc2] using flatPolynomial_degree_le J2
  have hd3 : (flatPolynomial J3).totalDegree ≤ 6 := by
    simpa only [hc3] using flatPolynomial_degree_le J3
  unfold targetPolynomial
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le ((MvPolynomial.totalDegree_add _ _).trans (max_le hd1 hd2)) hd3)

theorem eval_targetPolynomial : evalFun targetPolynomial = targetFunction := by
  funext x
  change MvPolynomial.eval x (flatPolynomial J1 + flatPolynomial J2 + flatPolynomial J3) =
    ind (coordSpan J1) x + ind (coordSpan J2) x + ind (coordSpan J3) x
  rw [map_add, map_add]
  change evalFun (flatPolynomial J1) x + evalFun (flatPolynomial J2) x +
    evalFun (flatPolynomial J3) x = _
  rw [eval_flatPolynomial, eval_flatPolynomial, eval_flatPolynomial]

theorem targetFunction_mem : targetFunction ∈ RM 6 12 :=
  ⟨targetPolynomial, targetPolynomial_degree, eval_targetPolynomial.symm⟩

/-- The masked coordinates all vanish. -/
def zeroMask (s a : ℕ) : Bool := Nat.beq (a &&& s) 0

theorem zeroMask_iff (s a : ℕ) (hs : s < 2 ^ 12) :
    zeroMask s a = true ↔ ∀ i : Fin 12, s.testBit i = true → a.testBit i = false := by
  unfold zeroMask
  constructor
  · intro h i hi
    have he : a &&& s = 0 := Nat.eq_of_beq_eq_true h
    have hbit := congrArg (fun n => n.testBit i) he
    simpa only [Nat.testBit_land, hi, Bool.and_true, Nat.zero_testBit] using hbit
  · intro h
    have he : a &&& s = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_land, Nat.zero_testBit]
      by_cases hj : j < 12
      · cases hsj : s.testBit j
        · simp
        · have hai := h ⟨j, hj⟩ hsj
          simp [hai]
      · have hlt : s < 2 ^ j :=
          lt_of_lt_of_le hs (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hsj : s.testBit j = false := Nat.testBit_eq_false_of_lt hlt
        simp [hsj]
    rw [he]
    exact Nat.beq_refl 0

/-- The reflection is pointwise for the actual coordinate-flat indicator. -/
theorem indicator_reflection (J : Finset ℕ) (s : ℕ) (hs : s < 2 ^ 12)
    (hmask : ∀ i : Fin 12, s.testBit i = true ↔ i.val + 1 ∉ J) (x : Pt 12) :
    ind (coordSpan J) x = if zeroMask s (Paper6Calib.pointEquiv x : ℕ) then 1 else 0 := by
  classical
  have hz : ∀ z : ZMod 2, decide (z = 1) = false ↔ z = 0 := by decide
  have hiff : zeroMask s (Paper6Calib.pointEquiv x : ℕ) = true ↔ x ∈ coordSpan J := by
    rw [zeroMask_iff s _ hs]
    change (∀ i : Fin 12, s.testBit i = true →
      (Paper6Calib.pointEquiv x : ℕ).testBit i = false) ↔
        ∀ i : Fin 12, i.val + 1 ∉ J → x i = 0
    simp only [hmask, Paper6Calib.testBit_pointEquiv, hz]
  by_cases hx : x ∈ coordSpan J
  · have hb := hiff.mpr hx
    simp [ind, hx, hb]
  · have hb : zeroMask s (Paper6Calib.pointEquiv x : ℕ) ≠ true :=
      fun h => hx (hiff.mp h)
    simp [ind, hx, hb]

/-- Complement masks: coordinates 7..12, 1..6, and 4..6 together with 10..12. -/
def bitValue (a : ℕ) : Bool :=
  xor (xor (zeroMask 4032 a) (zeroMask 63 a)) (zeroMask 3640 a)

theorem targetFunction_reflection (x : Pt 12) :
    targetFunction x = if bitValue (Paper6Calib.pointEquiv x : ℕ) then 1 else 0 := by
  have h1 := indicator_reflection J1 4032 (by decide) (by decide +kernel) x
  have h2 := indicator_reflection J2 63 (by decide) (by decide +kernel) x
  have h3 := indicator_reflection J3 3640 (by decide) (by decide +kernel) x
  change ind (coordSpan J1) x + ind (coordSpan J2) x + ind (coordSpan J3) x = _
  rw [h1, h2, h3]
  unfold bitValue
  cases zeroMask 4032 (Paper6Calib.pointEquiv x : ℕ) <;>
    cases zeroMask 63 (Paper6Calib.pointEquiv x : ℕ) <;>
    cases zeroMask 3640 (Paper6Calib.pointEquiv x : ℕ) <;> decide

theorem targetFunction_weight : hammingNorm targetFunction = 162 := by
  have hcard : hammingNorm targetFunction =
      #{a : Fin (2 ^ 12) | bitValue a.val = true} := by
    unfold hammingNorm
    apply Finset.card_equiv Paper6Calib.pointEquiv
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [targetFunction_reflection]
    cases bitValue (Paper6Calib.pointEquiv x : ℕ) <;> simp
  rw [hcard, Paper6Calib.card_fin_filter_eq_countP]
  decide +kernel

/-- Both conjuncts concern the exact function named by the frozen contract. -/
theorem check_RemD162 : BackfillPaper6.V3.RemD162 := by
  change targetFunction ∈ RM 6 12 ∧ hammingNorm targetFunction = 162
  exact ⟨targetFunction_mem, targetFunction_weight⟩

end Paper6Remark162

#print axioms Paper6Remark162.eval_flatPolynomial
#print axioms Paper6Remark162.flatPolynomial_degree_le
#print axioms Paper6Remark162.targetPolynomial_degree
#print axioms Paper6Remark162.eval_targetPolynomial
#print axioms Paper6Remark162.targetFunction_mem
#print axioms Paper6Remark162.zeroMask_iff
#print axioms Paper6Remark162.indicator_reflection
#print axioms Paper6Remark162.targetFunction_reflection
#print axioms Paper6Remark162.targetFunction_weight
#print axioms Paper6Remark162.check_RemD162
