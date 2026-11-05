import Research.Backfill.Paper7.ChallengeV3

/-!
# Paper 7: the frozen divided-difference recurrence

The equally spaced nodes turn the actual right-endpoint recurrence into
forward differences divided by a factorial. Gregory--Newton then proves
evaluation of the actual reconstruction at every supplied node. All bounds
include degree zero; no division by the characteristic is performed.
-/

set_option autoImplicit false

open Polynomial Finset
open BackfillPaper7.Challenge.Legacy.Algebra

namespace Paper7Interpolation

theorem node_injOn (ℓ d : ℕ) (hd : d < ℓ) :
    Set.InjOn (interpolationNode ℓ) (Finset.range (d + 1) : Set ℕ) := by
  intro i hi j hj hij
  have hiℓ : i < ℓ := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hd
  have hjℓ : j < ℓ := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hd
  have hsum : (i : ZMod ℓ) + 20 = (j : ZMod ℓ) + 20 := by
    simpa only [interpolationNode, Nat.cast_add, Nat.cast_ofNat] using hij
  have hcast : (i : ZMod ℓ) = (j : ZMod ℓ) := add_right_cancel hsum
  have hval := congrArg (fun z : ZMod ℓ => z.val) hcast
  simpa only [ZMod.val_natCast_of_lt hiℓ, ZMod.val_natCast_of_lt hjℓ] using hval

theorem node_backward_sub (ℓ i j : ℕ) (hji : j ≤ i) :
    interpolationNode ℓ i - interpolationNode ℓ (i - j) = (j : ZMod ℓ) := by
  simp only [interpolationNode, Nat.cast_add, Nat.cast_ofNat, Nat.cast_sub hji]
  ring

theorem factorial_cast_ne_zero (ℓ j : ℕ) [Fact ℓ.Prime] (hj : j < ℓ) :
    (j.factorial : ZMod ℓ) ≠ 0 :=
  ((IsUnit.natCast_factorial_iff_of_charP (A := ZMod ℓ) ℓ).mpr hj).ne_zero

/-- The right endpoint is i; all recursively inspected endpoints remain natural
and valid because j ≤ i. -/
theorem dividedDifference_eq_forward (ℓ : ℕ) [Fact ℓ.Prime]
    (values : ℕ → ZMod ℓ) (j i : ℕ) (hji : j ≤ i) (hj : j < ℓ) :
    dividedDifference ℓ values j i =
      ((fwdDiff (1 : ℕ))^[j] values) (i - j) / (j.factorial : ZMod ℓ) := by
  induction j generalizing i with
  | zero => simp [dividedDifference]
  | succ j ih =>
    have hji' : j ≤ i := by omega
    have hji1 : j ≤ i - 1 := by omega
    have hj' : j < ℓ := by omega
    have hjnz : ((j + 1 : ℕ) : ZMod ℓ) ≠ 0 := by
      intro hzero
      exact (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos j) hj)
        ((ZMod.natCast_eq_zero_iff (j + 1) ℓ).mp hzero)
    have hstep : ((fwdDiff (1 : ℕ))^[j + 1] values) (i - (j + 1)) =
        ((fwdDiff (1 : ℕ))^[j] values) (i - j) -
          ((fwdDiff (1 : ℕ))^[j] values) (i - 1 - j) := by
      rw [Function.iterate_succ_apply']
      change ((fwdDiff (1 : ℕ))^[j] values) (i - (j + 1) + 1) -
        ((fwdDiff (1 : ℕ))^[j] values) (i - (j + 1)) = _
      rw [show i - (j + 1) + 1 = i - j by omega,
        show i - (j + 1) = i - 1 - j by omega]
    rw [dividedDifference, node_backward_sub ℓ i (j + 1) hji,
      ih i hji' hj', ih (i - 1) hji1 hj', hstep,
      Nat.factorial_succ, Nat.cast_mul]
    field_simp [factorial_cast_ne_zero ℓ j hj', hjnz]

/-- The product vanishes when j exceeds n. This separate branch avoids
identifying a truncated natural subtraction with subtraction in the field. -/
theorem node_product_value (ℓ n j : ℕ) :
    (∏ i ∈ Finset.range j, (interpolationNode ℓ n - interpolationNode ℓ i)) =
      (j.factorial : ZMod ℓ) * (n.choose j : ZMod ℓ) := by
  by_cases hjn : j ≤ n
  · rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    have hin : i ≤ n := le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) hjn
    simp only [interpolationNode, Nat.cast_add, Nat.cast_ofNat, Nat.cast_sub hin]
    ring
  · have hnj : n < j := by omega
    rw [Nat.choose_eq_zero_of_lt hnj, Nat.cast_zero, mul_zero]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hnj) (sub_self _)

/-- The frozen Newton expression interpolates arbitrary values at its d+1
nodes. No polynomial hypothesis is needed for this assertion. -/
theorem reconstruction_eval (ℓ : ℕ) [Fact ℓ.Prime] (d : ℕ) (hd : d < ℓ)
    (values : ℕ → ZMod ℓ) (n : ℕ) (hn : n ≤ d) :
    (newtonReconstruction ℓ d values).eval (interpolationNode ℓ n) = values n := by
  have hterm : ∀ j ∈ Finset.range (d + 1),
      (C (dividedDifference ℓ values j j) *
        ∏ i ∈ Finset.range j, (X - C (interpolationNode ℓ i))).eval
            (interpolationNode ℓ n) =
        (n.choose j : ZMod ℓ) * ((fwdDiff (1 : ℕ))^[j] values) 0 := by
    intro j hj
    have hjℓ : j < ℓ := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hd
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [node_product_value, dividedDifference_eq_forward ℓ values j j le_rfl hjℓ,
      Nat.sub_self]
    field_simp [factorial_cast_ne_zero ℓ j hjℓ]
  unfold newtonReconstruction
  rw [Polynomial.eval_finsetSum]
  calc
    (∑ j ∈ Finset.range (d + 1),
      (C (dividedDifference ℓ values j j) *
        ∏ i ∈ Finset.range j, (X - C (interpolationNode ℓ i))).eval
          (interpolationNode ℓ n)) =
      ∑ j ∈ Finset.range (d + 1),
        (n.choose j : ZMod ℓ) * ((fwdDiff (1 : ℕ))^[j] values) 0 :=
      Finset.sum_congr rfl hterm
    _ = ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ZMod ℓ) * ((fwdDiff (1 : ℕ))^[j] values) 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hn 1))
      intro j _ hj
      have hj' : ¬ j < n + 1 := by simpa only [Finset.mem_range] using hj
      have hnj : n < j := by omega
      simp only [Nat.choose_eq_zero_of_lt hnj, Nat.cast_zero, zero_mul]
    _ = values n := by
      symm
      simpa only [zero_add, nsmul_eq_mul, Nat.cast_id, Nat.mul_one] using
        (shift_eq_sum_fwdDiff_iter (1 : ℕ) values n 0)

theorem reconstruction_natDegree_le (ℓ : ℕ) [Fact ℓ.Prime]
    (d : ℕ) (values : ℕ → ZMod ℓ) :
    (newtonReconstruction ℓ d values).natDegree ≤ d := by
  unfold newtonReconstruction
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  calc
    (C (dividedDifference ℓ values j j) *
        ∏ i ∈ Finset.range j, (X - C (interpolationNode ℓ i))).natDegree ≤
      (∏ i ∈ Finset.range j, (X - C (interpolationNode ℓ i))).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
    _ = j := by rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_range]
    _ ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)

theorem polynomial_unique (ℓ : ℕ) [Fact ℓ.Prime] (d : ℕ) (hd : d < ℓ)
    (f g : Polynomial (ZMod ℓ)) (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (heval : ∀ i ∈ Finset.range (d + 1),
      f.eval (interpolationNode ℓ i) = g.eval (interpolationNode ℓ i)) : f = g := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
    (Finset.range (d + 1)) (node_injOn ℓ d hd) _ _ heval
  · rw [Finset.card_range]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hf))
  · rw [Finset.card_range]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hg))

theorem reconstruction_exact (ℓ : ℕ) [Fact ℓ.Prime] (d : ℕ) (hd : d < ℓ)
    (f : Polynomial (ZMod ℓ)) (hf : f.natDegree ≤ d) :
    newtonReconstruction ℓ d (fun i => f.eval (interpolationNode ℓ i)) = f := by
  apply polynomial_unique ℓ d hd _ f (reconstruction_natDegree_le ℓ d _) hf
  intro i hi
  exact reconstruction_eval ℓ d hd _ i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

end Paper7Interpolation

#print axioms Paper7Interpolation.node_injOn
#print axioms Paper7Interpolation.node_backward_sub
#print axioms Paper7Interpolation.factorial_cast_ne_zero
#print axioms Paper7Interpolation.dividedDifference_eq_forward
#print axioms Paper7Interpolation.node_product_value
#print axioms Paper7Interpolation.reconstruction_eval
#print axioms Paper7Interpolation.reconstruction_natDegree_le
#print axioms Paper7Interpolation.polynomial_unique
#print axioms Paper7Interpolation.reconstruction_exact
