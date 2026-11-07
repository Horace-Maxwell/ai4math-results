import Research.Backfill.Paper2.Challenge

namespace BackfillPaper2.ReviewRegressionTests
open PowerSeries BackfillPaper2.Challenge

/-- Probe 1: `A = x` solves the A389472 equation (the solutions are `x + t·K`; `a(2)` is free),
so `EX_A389472` needs the normalization `a(2) = 1`, which it has. -/
theorem review_regression_01 : Eq389472 (X : PowerSeries ℤ) := by
  have ha : HasSubst ((X : PowerSeries ℤ) ^ 2 + X ^ 3) := HasSubst.of_constantCoeff_zero' (by simp)
  unfold Eq389472
  rw [subst_X ha]
  ring

/-- Probe 2: `Ring.choose (1/2 : ℚ) 1 = 1/2`. -/
theorem review_regression_02 : Ring.choose (1 / 2 : ℚ) 1 = 1 / 2 := by
  simp

/-- Probe 3: the first nontrivial coefficient of `sqrtSeries3` (`x^3`, `j = 1`) is
`binom(1/2, 1) = 1/2 ≡ 2 (mod 3)`: exercises `Ring.choose` and the cast `ℚ → ZMod 3` at `j ≥ 1`. -/
theorem coeff3_sqrtSeries3 : coeff 3 sqrtSeries3 = 2 := by
  have h : ((Ring.choose (1 / 2 : ℚ) 1 : ℚ) : ZMod 3) = 2 := by
    rw [Ring.choose_one_right, Rat.cast_div_of_ne_zero (by norm_num) (by decide)]
    norm_num
    exact inv_eq_of_mul_eq_one_right (by decide)
  rw [← h, sqrtSeries3, coeff_mk, Finset.sum_eq_single 1]
  · simp
  · intro j _ hj
    rw [ite_eq_right]
    intro h3
    exact hj (Nat.pow_right_injective (by norm_num : 2 ≤ 3) (h3.symm.trans (pow_one 3).symm))
  · intro h1
    exact absurd (Finset.mem_range.mpr (by norm_num)) h1

/-- Probe 4 (false instance): the `x^3` coefficient of `sqrtSeries3` is not `1`. -/
theorem review_regression_03 : coeff 3 sqrtSeries3 ≠ 1 := by
  rw [coeff3_sqrtSeries3]
  decide

theorem coeff9_sqrtSeries3 : coeff 9 sqrtSeries3 = 1 := by
  have h : ((Ring.choose (1 / 2 : ℚ) 2 : ℚ) : ZMod 3) = 1 := by
    have hc : Ring.choose (1 / 2 : ℚ) 2 = -1 / 8 := by
      rw [Ring.choose_eq_smul, show (2 : ℕ) = 1 + 1 from rfl,
        descPochhammer_succ_right]
      norm_num [Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_natCast]
    rw [hc, Rat.cast_div_of_ne_zero (by norm_num) (by decide)]
    have he : (((-1 : ℚ) : ZMod 3)) = ((8 : ℚ) : ZMod 3) := by
      norm_num
      decide
    rw [he]
    exact div_self (by norm_num; decide)
  rw [sqrtSeries3, coeff_mk, Finset.sum_eq_single 2]
  · simpa using h
  · intro j _ hj
    rw [ite_eq_right]
    intro h9
    exact hj (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h9.symm)
  · intro h2
    exact absurd (Finset.mem_range.mpr (by norm_num)) h2

theorem coeff1_ternarySeries : coeff 1 ternarySeries = 1 := by
  simp [ternarySeries, ternary]

theorem coeff0_ternarySeries : coeff 0 ternarySeries = 0 := by
  simp [ternarySeries]

end BackfillPaper2.ReviewRegressionTests

#print axioms BackfillPaper2.ReviewRegressionTests.review_regression_01
#print axioms BackfillPaper2.ReviewRegressionTests.review_regression_02
#print axioms BackfillPaper2.ReviewRegressionTests.coeff3_sqrtSeries3
#print axioms BackfillPaper2.ReviewRegressionTests.review_regression_03
#print axioms BackfillPaper2.ReviewRegressionTests.coeff9_sqrtSeries3
#print axioms BackfillPaper2.ReviewRegressionTests.coeff1_ternarySeries
#print axioms BackfillPaper2.ReviewRegressionTests.coeff0_ternarySeries
