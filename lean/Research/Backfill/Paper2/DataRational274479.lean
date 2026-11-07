import Research.Backfill.Paper2.FiniteCoefficients

/-! Finite exact convolution certificates for every original normalized solution. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.DataRational274479
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.FiniteCoefficients

private def D : PowerSeries ℤ := 1 - 2 * X - 4 * X ^ 2
private def E : PowerSeries ℤ := invOfUnit D 1
private def h : PowerSeries ℤ := X ^ 2 * E

private theorem cell_hh0 : constantCoeff h = 0 := by
  exact by simp [h]

private theorem cell_hDE : D * E = 1 := by
  exact mul_invOfUnit D 1 (by simp [D])

private theorem cell_ha0 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0) : coeff 0 A = 0 := by
  exact by simpa only [coeff_zero_eq_constantCoeff_apply] using h0

private theorem cell_ha1 (A : PowerSeries ℤ) (h1 : coeff 1 A = 1) : coeff 1 A = 1 := by
  exact h1

private theorem cell_e0 (hDE : D * E = 1) : coeff 0 E = 1 := by
  have he := congrArg constantCoeff hDE
  have hc : constantCoeff E = 1 := by simpa [D] using he
  simpa only [coeff_zero_eq_constantCoeff_apply] using hc

private theorem cell_h0 (_e0 : coeff 0 E = 1) : coeff 0 h = 0 := by
  norm_num [h, coeff_X_pow_mul', _e0]

private theorem cell_p2_0 (h0 : coeff 0 h = 0) : coeff 0 (h ^ 2) = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0]

private theorem cell_p3_0 (h0 : coeff 0 h = 0) (_p2_0 : coeff 0 (h ^ 2) = 0) : coeff 0 (h ^ 3) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, _p2_0]

private theorem cell_p4_0 (h0 : coeff 0 h = 0) (_p3_0 : coeff 0 (h ^ 3) = 0) : coeff 0 (h ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, _p3_0]

private theorem cell_p5_0 (h0 : coeff 0 h = 0) (_p4_0 : coeff 0 (h ^ 4) = 0) : coeff 0 (h ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, _p4_0]

private theorem cell_p6_0 (h0 : coeff 0 h = 0) (_p5_0 : coeff 0 (h ^ 5) = 0) : coeff 0 (h ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, _p5_0]

private theorem cell_p7_0 (h0 : coeff 0 h = 0) (_p6_0 : coeff 0 (h ^ 6) = 0) : coeff 0 (h ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, _p6_0]

private theorem cell_e1 (hDE : D * E = 1) (e0 : coeff 0 E = 1) : coeff 1 E = 2 := by
  have he := congrArg (coeff 1) hDE
  norm_num [D, coeff_mul_range, Finset.sum_range_succ, coeff_X, coeff_X_pow, e0] at he
  omega

private theorem cell_h1 (_e0 : coeff 0 E = 1) (_e1 : coeff 1 E = 2) : coeff 1 h = 0 := by
  norm_num [h, coeff_X_pow_mul', _e0, _e1]

private theorem cell_p2_1 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) : coeff 1 (h ^ 2) = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1]

private theorem cell_p3_1 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p2_0 : coeff 0 (h ^ 2) = 0) (p2_1 : coeff 1 (h ^ 2) = 0) : coeff 1 (h ^ 3) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, p2_0, p2_1]

private theorem cell_p4_1 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p3_0 : coeff 0 (h ^ 3) = 0) (p3_1 : coeff 1 (h ^ 3) = 0) : coeff 1 (h ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, p3_0, p3_1]

private theorem cell_p5_1 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p4_0 : coeff 0 (h ^ 4) = 0) (p4_1 : coeff 1 (h ^ 4) = 0) : coeff 1 (h ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, p4_0, p4_1]

private theorem cell_p6_1 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p5_0 : coeff 0 (h ^ 5) = 0) (p5_1 : coeff 1 (h ^ 5) = 0) : coeff 1 (h ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, p5_0, p5_1]

private theorem cell_p7_1 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p6_0 : coeff 0 (h ^ 6) = 0) (p6_1 : coeff 1 (h ^ 6) = 0) : coeff 1 (h ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, p6_0, p6_1]

private theorem cell_e2 (hDE : D * E = 1) (e0 : coeff 0 E = 1) (e1 : coeff 1 E = 2) : coeff 2 E = 8 := by
  have he := congrArg (coeff 2) hDE
  norm_num [D, coeff_mul_range, Finset.sum_range_succ, coeff_X, coeff_X_pow, e0, e1] at he
  omega

private theorem cell_h2 (e0 : coeff 0 E = 1) (_e1 : coeff 1 E = 2) (_e2 : coeff 2 E = 8) : coeff 2 h = 1 := by
  norm_num [h, coeff_X_pow_mul', e0, _e1, _e2]

private theorem cell_p2_2 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (h2 : coeff 2 h = 1) : coeff 2 (h ^ 2) = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2]

private theorem cell_p3_2 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p2_0 : coeff 0 (h ^ 2) = 0) (p2_1 : coeff 1 (h ^ 2) = 0) (h2 : coeff 2 h = 1) (p2_2 : coeff 2 (h ^ 2) = 0) : coeff 2 (h ^ 3) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, p2_0, p2_1, p2_2]

private theorem cell_p4_2 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p3_0 : coeff 0 (h ^ 3) = 0) (p3_1 : coeff 1 (h ^ 3) = 0) (h2 : coeff 2 h = 1) (p3_2 : coeff 2 (h ^ 3) = 0) : coeff 2 (h ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, p3_0, p3_1, p3_2]

private theorem cell_p5_2 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p4_0 : coeff 0 (h ^ 4) = 0) (p4_1 : coeff 1 (h ^ 4) = 0) (h2 : coeff 2 h = 1) (p4_2 : coeff 2 (h ^ 4) = 0) : coeff 2 (h ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, p4_0, p4_1, p4_2]

private theorem cell_p6_2 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p5_0 : coeff 0 (h ^ 5) = 0) (p5_1 : coeff 1 (h ^ 5) = 0) (h2 : coeff 2 h = 1) (p5_2 : coeff 2 (h ^ 5) = 0) : coeff 2 (h ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, p5_0, p5_1, p5_2]

private theorem cell_p7_2 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p6_0 : coeff 0 (h ^ 6) = 0) (p6_1 : coeff 1 (h ^ 6) = 0) (h2 : coeff 2 h = 1) (p6_2 : coeff 2 (h ^ 6) = 0) : coeff 2 (h ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, p6_0, p6_1, p6_2]

private theorem cell_e3 (hDE : D * E = 1) (e0 : coeff 0 E = 1) (e1 : coeff 1 E = 2) (e2 : coeff 2 E = 8) : coeff 3 E = 24 := by
  have he := congrArg (coeff 3) hDE
  norm_num [D, coeff_mul_range, Finset.sum_range_succ, coeff_X, coeff_X_pow, e0, e1, e2] at he
  omega

private theorem cell_h3 (_e0 : coeff 0 E = 1) (e1 : coeff 1 E = 2) (_e2 : coeff 2 E = 8) (_e3 : coeff 3 E = 24) : coeff 3 h = 2 := by
  norm_num [h, coeff_X_pow_mul', _e0, e1, _e2, _e3]

private theorem cell_p2_3 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (h2 : coeff 2 h = 1) (h3 : coeff 3 h = 2) : coeff 3 (h ^ 2) = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3]

private theorem cell_p3_3 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p2_0 : coeff 0 (h ^ 2) = 0) (p2_1 : coeff 1 (h ^ 2) = 0) (h2 : coeff 2 h = 1) (p2_2 : coeff 2 (h ^ 2) = 0) (h3 : coeff 3 h = 2) (p2_3 : coeff 3 (h ^ 2) = 0) : coeff 3 (h ^ 3) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, p2_0, p2_1, p2_2, p2_3]

private theorem cell_p4_3 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p3_0 : coeff 0 (h ^ 3) = 0) (p3_1 : coeff 1 (h ^ 3) = 0) (h2 : coeff 2 h = 1) (p3_2 : coeff 2 (h ^ 3) = 0) (h3 : coeff 3 h = 2) (p3_3 : coeff 3 (h ^ 3) = 0) : coeff 3 (h ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, p3_0, p3_1, p3_2, p3_3]

private theorem cell_p5_3 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p4_0 : coeff 0 (h ^ 4) = 0) (p4_1 : coeff 1 (h ^ 4) = 0) (h2 : coeff 2 h = 1) (p4_2 : coeff 2 (h ^ 4) = 0) (h3 : coeff 3 h = 2) (p4_3 : coeff 3 (h ^ 4) = 0) : coeff 3 (h ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, p4_0, p4_1, p4_2, p4_3]

private theorem cell_p6_3 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p5_0 : coeff 0 (h ^ 5) = 0) (p5_1 : coeff 1 (h ^ 5) = 0) (h2 : coeff 2 h = 1) (p5_2 : coeff 2 (h ^ 5) = 0) (h3 : coeff 3 h = 2) (p5_3 : coeff 3 (h ^ 5) = 0) : coeff 3 (h ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, p5_0, p5_1, p5_2, p5_3]

private theorem cell_p7_3 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p6_0 : coeff 0 (h ^ 6) = 0) (p6_1 : coeff 1 (h ^ 6) = 0) (h2 : coeff 2 h = 1) (p6_2 : coeff 2 (h ^ 6) = 0) (h3 : coeff 3 h = 2) (p6_3 : coeff 3 (h ^ 6) = 0) : coeff 3 (h ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, p6_0, p6_1, p6_2, p6_3]

private theorem cell_e4 (hDE : D * E = 1) (e0 : coeff 0 E = 1) (e1 : coeff 1 E = 2) (e2 : coeff 2 E = 8) (e3 : coeff 3 E = 24) : coeff 4 E = 80 := by
  have he := congrArg (coeff 4) hDE
  norm_num [D, coeff_mul_range, Finset.sum_range_succ, coeff_X, coeff_X_pow, e0, e1, e2, e3] at he
  omega

private theorem cell_h4 (_e0 : coeff 0 E = 1) (_e1 : coeff 1 E = 2) (e2 : coeff 2 E = 8) (_e3 : coeff 3 E = 24) (_e4 : coeff 4 E = 80) : coeff 4 h = 8 := by
  norm_num [h, coeff_X_pow_mul', _e0, _e1, e2, _e3, _e4]

private theorem cell_p2_4 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (h2 : coeff 2 h = 1) (h3 : coeff 3 h = 2) (h4 : coeff 4 h = 8) : coeff 4 (h ^ 2) = 1 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4]

private theorem cell_p3_4 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p2_0 : coeff 0 (h ^ 2) = 0) (p2_1 : coeff 1 (h ^ 2) = 0) (h2 : coeff 2 h = 1) (p2_2 : coeff 2 (h ^ 2) = 0) (h3 : coeff 3 h = 2) (p2_3 : coeff 3 (h ^ 2) = 0) (h4 : coeff 4 h = 8) (p2_4 : coeff 4 (h ^ 2) = 1) : coeff 4 (h ^ 3) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, p2_0, p2_1, p2_2, p2_3, p2_4]

private theorem cell_p4_4 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p3_0 : coeff 0 (h ^ 3) = 0) (p3_1 : coeff 1 (h ^ 3) = 0) (h2 : coeff 2 h = 1) (p3_2 : coeff 2 (h ^ 3) = 0) (h3 : coeff 3 h = 2) (p3_3 : coeff 3 (h ^ 3) = 0) (h4 : coeff 4 h = 8) (p3_4 : coeff 4 (h ^ 3) = 0) : coeff 4 (h ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, p3_0, p3_1, p3_2, p3_3, p3_4]

private theorem cell_p5_4 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p4_0 : coeff 0 (h ^ 4) = 0) (p4_1 : coeff 1 (h ^ 4) = 0) (h2 : coeff 2 h = 1) (p4_2 : coeff 2 (h ^ 4) = 0) (h3 : coeff 3 h = 2) (p4_3 : coeff 3 (h ^ 4) = 0) (h4 : coeff 4 h = 8) (p4_4 : coeff 4 (h ^ 4) = 0) : coeff 4 (h ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, p4_0, p4_1, p4_2, p4_3, p4_4]

private theorem cell_p6_4 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p5_0 : coeff 0 (h ^ 5) = 0) (p5_1 : coeff 1 (h ^ 5) = 0) (h2 : coeff 2 h = 1) (p5_2 : coeff 2 (h ^ 5) = 0) (h3 : coeff 3 h = 2) (p5_3 : coeff 3 (h ^ 5) = 0) (h4 : coeff 4 h = 8) (p5_4 : coeff 4 (h ^ 5) = 0) : coeff 4 (h ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, p5_0, p5_1, p5_2, p5_3, p5_4]

private theorem cell_p7_4 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p6_0 : coeff 0 (h ^ 6) = 0) (p6_1 : coeff 1 (h ^ 6) = 0) (h2 : coeff 2 h = 1) (p6_2 : coeff 2 (h ^ 6) = 0) (h3 : coeff 3 h = 2) (p6_3 : coeff 3 (h ^ 6) = 0) (h4 : coeff 4 h = 8) (p6_4 : coeff 4 (h ^ 6) = 0) : coeff 4 (h ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, p6_0, p6_1, p6_2, p6_3, p6_4]

private theorem cell_e5 (hDE : D * E = 1) (e0 : coeff 0 E = 1) (e1 : coeff 1 E = 2) (e2 : coeff 2 E = 8) (e3 : coeff 3 E = 24) (e4 : coeff 4 E = 80) : coeff 5 E = 256 := by
  have he := congrArg (coeff 5) hDE
  norm_num [D, coeff_mul_range, Finset.sum_range_succ, coeff_X, coeff_X_pow, e0, e1, e2, e3, e4] at he
  omega

private theorem cell_h5 (_e0 : coeff 0 E = 1) (_e1 : coeff 1 E = 2) (_e2 : coeff 2 E = 8) (e3 : coeff 3 E = 24) (_e4 : coeff 4 E = 80) (_e5 : coeff 5 E = 256) : coeff 5 h = 24 := by
  norm_num [h, coeff_X_pow_mul', _e0, _e1, _e2, e3, _e4, _e5]

private theorem cell_p2_5 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (h2 : coeff 2 h = 1) (h3 : coeff 3 h = 2) (h4 : coeff 4 h = 8) (h5 : coeff 5 h = 24) : coeff 5 (h ^ 2) = 4 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5]

private theorem cell_p3_5 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p2_0 : coeff 0 (h ^ 2) = 0) (p2_1 : coeff 1 (h ^ 2) = 0) (h2 : coeff 2 h = 1) (p2_2 : coeff 2 (h ^ 2) = 0) (h3 : coeff 3 h = 2) (p2_3 : coeff 3 (h ^ 2) = 0) (h4 : coeff 4 h = 8) (p2_4 : coeff 4 (h ^ 2) = 1) (h5 : coeff 5 h = 24) (p2_5 : coeff 5 (h ^ 2) = 4) : coeff 5 (h ^ 3) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, p2_0, p2_1, p2_2, p2_3, p2_4, p2_5]

private theorem cell_p4_5 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p3_0 : coeff 0 (h ^ 3) = 0) (p3_1 : coeff 1 (h ^ 3) = 0) (h2 : coeff 2 h = 1) (p3_2 : coeff 2 (h ^ 3) = 0) (h3 : coeff 3 h = 2) (p3_3 : coeff 3 (h ^ 3) = 0) (h4 : coeff 4 h = 8) (p3_4 : coeff 4 (h ^ 3) = 0) (h5 : coeff 5 h = 24) (p3_5 : coeff 5 (h ^ 3) = 0) : coeff 5 (h ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, p3_0, p3_1, p3_2, p3_3, p3_4, p3_5]

private theorem cell_p5_5 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p4_0 : coeff 0 (h ^ 4) = 0) (p4_1 : coeff 1 (h ^ 4) = 0) (h2 : coeff 2 h = 1) (p4_2 : coeff 2 (h ^ 4) = 0) (h3 : coeff 3 h = 2) (p4_3 : coeff 3 (h ^ 4) = 0) (h4 : coeff 4 h = 8) (p4_4 : coeff 4 (h ^ 4) = 0) (h5 : coeff 5 h = 24) (p4_5 : coeff 5 (h ^ 4) = 0) : coeff 5 (h ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, p4_0, p4_1, p4_2, p4_3, p4_4, p4_5]

private theorem cell_p6_5 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p5_0 : coeff 0 (h ^ 5) = 0) (p5_1 : coeff 1 (h ^ 5) = 0) (h2 : coeff 2 h = 1) (p5_2 : coeff 2 (h ^ 5) = 0) (h3 : coeff 3 h = 2) (p5_3 : coeff 3 (h ^ 5) = 0) (h4 : coeff 4 h = 8) (p5_4 : coeff 4 (h ^ 5) = 0) (h5 : coeff 5 h = 24) (p5_5 : coeff 5 (h ^ 5) = 0) : coeff 5 (h ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, p5_0, p5_1, p5_2, p5_3, p5_4, p5_5]

private theorem cell_p7_5 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p6_0 : coeff 0 (h ^ 6) = 0) (p6_1 : coeff 1 (h ^ 6) = 0) (h2 : coeff 2 h = 1) (p6_2 : coeff 2 (h ^ 6) = 0) (h3 : coeff 3 h = 2) (p6_3 : coeff 3 (h ^ 6) = 0) (h4 : coeff 4 h = 8) (p6_4 : coeff 4 (h ^ 6) = 0) (h5 : coeff 5 h = 24) (p6_5 : coeff 5 (h ^ 6) = 0) : coeff 5 (h ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, p6_0, p6_1, p6_2, p6_3, p6_4, p6_5]

private theorem cell_e6 (hDE : D * E = 1) (e0 : coeff 0 E = 1) (e1 : coeff 1 E = 2) (e2 : coeff 2 E = 8) (e3 : coeff 3 E = 24) (e4 : coeff 4 E = 80) (e5 : coeff 5 E = 256) : coeff 6 E = 832 := by
  have he := congrArg (coeff 6) hDE
  norm_num [D, coeff_mul_range, Finset.sum_range_succ, coeff_X, coeff_X_pow, e0, e1, e2, e3, e4, e5] at he
  omega

private theorem cell_h6 (_e0 : coeff 0 E = 1) (_e1 : coeff 1 E = 2) (_e2 : coeff 2 E = 8) (_e3 : coeff 3 E = 24) (e4 : coeff 4 E = 80) (_e5 : coeff 5 E = 256) (_e6 : coeff 6 E = 832) : coeff 6 h = 80 := by
  norm_num [h, coeff_X_pow_mul', _e0, _e1, _e2, _e3, e4, _e5, _e6]

private theorem cell_p2_6 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (h2 : coeff 2 h = 1) (h3 : coeff 3 h = 2) (h4 : coeff 4 h = 8) (h5 : coeff 5 h = 24) (h6 : coeff 6 h = 80) : coeff 6 (h ^ 2) = 20 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, h6]

private theorem cell_p3_6 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p2_0 : coeff 0 (h ^ 2) = 0) (p2_1 : coeff 1 (h ^ 2) = 0) (h2 : coeff 2 h = 1) (p2_2 : coeff 2 (h ^ 2) = 0) (h3 : coeff 3 h = 2) (p2_3 : coeff 3 (h ^ 2) = 0) (h4 : coeff 4 h = 8) (p2_4 : coeff 4 (h ^ 2) = 1) (h5 : coeff 5 h = 24) (p2_5 : coeff 5 (h ^ 2) = 4) (h6 : coeff 6 h = 80) (p2_6 : coeff 6 (h ^ 2) = 20) : coeff 6 (h ^ 3) = 1 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, h6, p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6]

private theorem cell_p4_6 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p3_0 : coeff 0 (h ^ 3) = 0) (p3_1 : coeff 1 (h ^ 3) = 0) (h2 : coeff 2 h = 1) (p3_2 : coeff 2 (h ^ 3) = 0) (h3 : coeff 3 h = 2) (p3_3 : coeff 3 (h ^ 3) = 0) (h4 : coeff 4 h = 8) (p3_4 : coeff 4 (h ^ 3) = 0) (h5 : coeff 5 h = 24) (p3_5 : coeff 5 (h ^ 3) = 0) (h6 : coeff 6 h = 80) (p3_6 : coeff 6 (h ^ 3) = 1) : coeff 6 (h ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, h6, p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6]

private theorem cell_p5_6 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p4_0 : coeff 0 (h ^ 4) = 0) (p4_1 : coeff 1 (h ^ 4) = 0) (h2 : coeff 2 h = 1) (p4_2 : coeff 2 (h ^ 4) = 0) (h3 : coeff 3 h = 2) (p4_3 : coeff 3 (h ^ 4) = 0) (h4 : coeff 4 h = 8) (p4_4 : coeff 4 (h ^ 4) = 0) (h5 : coeff 5 h = 24) (p4_5 : coeff 5 (h ^ 4) = 0) (h6 : coeff 6 h = 80) (p4_6 : coeff 6 (h ^ 4) = 0) : coeff 6 (h ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, h6, p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6]

private theorem cell_p6_6 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p5_0 : coeff 0 (h ^ 5) = 0) (p5_1 : coeff 1 (h ^ 5) = 0) (h2 : coeff 2 h = 1) (p5_2 : coeff 2 (h ^ 5) = 0) (h3 : coeff 3 h = 2) (p5_3 : coeff 3 (h ^ 5) = 0) (h4 : coeff 4 h = 8) (p5_4 : coeff 4 (h ^ 5) = 0) (h5 : coeff 5 h = 24) (p5_5 : coeff 5 (h ^ 5) = 0) (h6 : coeff 6 h = 80) (p5_6 : coeff 6 (h ^ 5) = 0) : coeff 6 (h ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, h6, p5_0, p5_1, p5_2, p5_3, p5_4, p5_5, p5_6]

private theorem cell_p7_6 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p6_0 : coeff 0 (h ^ 6) = 0) (p6_1 : coeff 1 (h ^ 6) = 0) (h2 : coeff 2 h = 1) (p6_2 : coeff 2 (h ^ 6) = 0) (h3 : coeff 3 h = 2) (p6_3 : coeff 3 (h ^ 6) = 0) (h4 : coeff 4 h = 8) (p6_4 : coeff 4 (h ^ 6) = 0) (h5 : coeff 5 h = 24) (p6_5 : coeff 5 (h ^ 6) = 0) (h6 : coeff 6 h = 80) (p6_6 : coeff 6 (h ^ 6) = 0) : coeff 6 (h ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, h6, p6_0, p6_1, p6_2, p6_3, p6_4, p6_5, p6_6]

private theorem cell_e7 (hDE : D * E = 1) (e0 : coeff 0 E = 1) (e1 : coeff 1 E = 2) (e2 : coeff 2 E = 8) (e3 : coeff 3 E = 24) (e4 : coeff 4 E = 80) (e5 : coeff 5 E = 256) (e6 : coeff 6 E = 832) : coeff 7 E = 2688 := by
  have he := congrArg (coeff 7) hDE
  norm_num [D, coeff_mul_range, Finset.sum_range_succ, coeff_X, coeff_X_pow, e0, e1, e2, e3, e4, e5, e6] at he
  omega

private theorem cell_h7 (_e0 : coeff 0 E = 1) (_e1 : coeff 1 E = 2) (_e2 : coeff 2 E = 8) (_e3 : coeff 3 E = 24) (_e4 : coeff 4 E = 80) (e5 : coeff 5 E = 256) (_e6 : coeff 6 E = 832) (_e7 : coeff 7 E = 2688) : coeff 7 h = 256 := by
  norm_num [h, coeff_X_pow_mul', _e0, _e1, _e2, _e3, _e4, e5, _e6, _e7]

private theorem cell_p2_7 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (h2 : coeff 2 h = 1) (h3 : coeff 3 h = 2) (h4 : coeff 4 h = 8) (h5 : coeff 5 h = 24) (h6 : coeff 6 h = 80) (h7 : coeff 7 h = 256) : coeff 7 (h ^ 2) = 80 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, h6, h7]

private theorem cell_p3_7 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p2_0 : coeff 0 (h ^ 2) = 0) (p2_1 : coeff 1 (h ^ 2) = 0) (h2 : coeff 2 h = 1) (p2_2 : coeff 2 (h ^ 2) = 0) (h3 : coeff 3 h = 2) (p2_3 : coeff 3 (h ^ 2) = 0) (h4 : coeff 4 h = 8) (p2_4 : coeff 4 (h ^ 2) = 1) (h5 : coeff 5 h = 24) (p2_5 : coeff 5 (h ^ 2) = 4) (h6 : coeff 6 h = 80) (p2_6 : coeff 6 (h ^ 2) = 20) (h7 : coeff 7 h = 256) (p2_7 : coeff 7 (h ^ 2) = 80) : coeff 7 (h ^ 3) = 6 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, h6, h7, p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7]

private theorem cell_p4_7 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p3_0 : coeff 0 (h ^ 3) = 0) (p3_1 : coeff 1 (h ^ 3) = 0) (h2 : coeff 2 h = 1) (p3_2 : coeff 2 (h ^ 3) = 0) (h3 : coeff 3 h = 2) (p3_3 : coeff 3 (h ^ 3) = 0) (h4 : coeff 4 h = 8) (p3_4 : coeff 4 (h ^ 3) = 0) (h5 : coeff 5 h = 24) (p3_5 : coeff 5 (h ^ 3) = 0) (h6 : coeff 6 h = 80) (p3_6 : coeff 6 (h ^ 3) = 1) (h7 : coeff 7 h = 256) (p3_7 : coeff 7 (h ^ 3) = 6) : coeff 7 (h ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, h6, h7, p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7]

private theorem cell_p5_7 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p4_0 : coeff 0 (h ^ 4) = 0) (p4_1 : coeff 1 (h ^ 4) = 0) (h2 : coeff 2 h = 1) (p4_2 : coeff 2 (h ^ 4) = 0) (h3 : coeff 3 h = 2) (p4_3 : coeff 3 (h ^ 4) = 0) (h4 : coeff 4 h = 8) (p4_4 : coeff 4 (h ^ 4) = 0) (h5 : coeff 5 h = 24) (p4_5 : coeff 5 (h ^ 4) = 0) (h6 : coeff 6 h = 80) (p4_6 : coeff 6 (h ^ 4) = 0) (h7 : coeff 7 h = 256) (p4_7 : coeff 7 (h ^ 4) = 0) : coeff 7 (h ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, h6, h7, p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7]

private theorem cell_p6_7 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p5_0 : coeff 0 (h ^ 5) = 0) (p5_1 : coeff 1 (h ^ 5) = 0) (h2 : coeff 2 h = 1) (p5_2 : coeff 2 (h ^ 5) = 0) (h3 : coeff 3 h = 2) (p5_3 : coeff 3 (h ^ 5) = 0) (h4 : coeff 4 h = 8) (p5_4 : coeff 4 (h ^ 5) = 0) (h5 : coeff 5 h = 24) (p5_5 : coeff 5 (h ^ 5) = 0) (h6 : coeff 6 h = 80) (p5_6 : coeff 6 (h ^ 5) = 0) (h7 : coeff 7 h = 256) (p5_7 : coeff 7 (h ^ 5) = 0) : coeff 7 (h ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, h6, h7, p5_0, p5_1, p5_2, p5_3, p5_4, p5_5, p5_6, p5_7]

private theorem cell_p7_7 (h0 : coeff 0 h = 0) (h1 : coeff 1 h = 0) (p6_0 : coeff 0 (h ^ 6) = 0) (p6_1 : coeff 1 (h ^ 6) = 0) (h2 : coeff 2 h = 1) (p6_2 : coeff 2 (h ^ 6) = 0) (h3 : coeff 3 h = 2) (p6_3 : coeff 3 (h ^ 6) = 0) (h4 : coeff 4 h = 8) (p6_4 : coeff 4 (h ^ 6) = 0) (h5 : coeff 5 h = 24) (p6_5 : coeff 5 (h ^ 6) = 0) (h6 : coeff 6 h = 80) (p6_6 : coeff 6 (h ^ 6) = 0) (h7 : coeff 7 h = 256) (p6_7 : coeff 7 (h ^ 6) = 0) : coeff 7 (h ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, h6, h7, p6_0, p6_1, p6_2, p6_3, p6_4, p6_5, p6_6, p6_7]

private theorem cell_ha2 (A : PowerSeries ℤ) (_h0 : coeff 0 h = 0) (_h1 : coeff 1 h = 0) (hA : A * A = A.subst h) (hh0 : constantCoeff h = 0) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (_h2 : coeff 2 h = 1) (h3 : coeff 3 h = 2) (p2_3 : coeff 3 (h ^ 2) = 0) (p3_3 : coeff 3 (h ^ 3) = 0) (_p4_3 : coeff 3 (h ^ 4) = 0) (_p5_3 : coeff 3 (h ^ 5) = 0) (_p6_3 : coeff 3 (h ^ 6) = 0) (_p7_3 : coeff 3 (h ^ 7) = 0) (_h4 : coeff 4 h = 8) (_h5 : coeff 5 h = 24) (_h6 : coeff 6 h = 80) (_h7 : coeff 7 h = 256) : coeff 2 A = 1 := by
  have he := congrArg (coeff 3) hA
  norm_num [coeff_mul_range, coeff_subst_range _ _ hh0, Finset.sum_range_succ, ha0, ha1, _h0, _h1, _h2, h3, _h4, _h5, _h6, _h7, p2_3, p3_3, _p4_3, _p5_3, _p6_3, _p7_3] at he
  nlinarith [he]

private theorem cell_ha3 (A : PowerSeries ℤ) (_h0 : coeff 0 h = 0) (_h1 : coeff 1 h = 0) (hA : A * A = A.subst h) (hh0 : constantCoeff h = 0) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (_h2 : coeff 2 h = 1) (_h3 : coeff 3 h = 2) (h4 : coeff 4 h = 8) (p2_4 : coeff 4 (h ^ 2) = 1) (p3_4 : coeff 4 (h ^ 3) = 0) (p4_4 : coeff 4 (h ^ 4) = 0) (_p5_4 : coeff 4 (h ^ 5) = 0) (_p6_4 : coeff 4 (h ^ 6) = 0) (_p7_4 : coeff 4 (h ^ 7) = 0) (_h5 : coeff 5 h = 24) (_h6 : coeff 6 h = 80) (_h7 : coeff 7 h = 256) (ha2 : coeff 2 A = 1) : coeff 3 A = 4 := by
  have he := congrArg (coeff 4) hA
  norm_num [coeff_mul_range, coeff_subst_range _ _ hh0, Finset.sum_range_succ, ha0, ha1, ha2, _h0, _h1, _h2, _h3, h4, _h5, _h6, _h7, p2_4, p3_4, p4_4, _p5_4, _p6_4, _p7_4] at he
  nlinarith [he]

private theorem cell_ha4 (A : PowerSeries ℤ) (_h0 : coeff 0 h = 0) (_h1 : coeff 1 h = 0) (hA : A * A = A.subst h) (hh0 : constantCoeff h = 0) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (_h2 : coeff 2 h = 1) (_h3 : coeff 3 h = 2) (_h4 : coeff 4 h = 8) (h5 : coeff 5 h = 24) (p2_5 : coeff 5 (h ^ 2) = 4) (p3_5 : coeff 5 (h ^ 3) = 0) (p4_5 : coeff 5 (h ^ 4) = 0) (p5_5 : coeff 5 (h ^ 5) = 0) (_p6_5 : coeff 5 (h ^ 6) = 0) (_p7_5 : coeff 5 (h ^ 7) = 0) (_h6 : coeff 6 h = 80) (_h7 : coeff 7 h = 256) (ha2 : coeff 2 A = 1) (ha3 : coeff 3 A = 4) : coeff 4 A = 10 := by
  have he := congrArg (coeff 5) hA
  norm_num [coeff_mul_range, coeff_subst_range _ _ hh0, Finset.sum_range_succ, ha0, ha1, ha2, ha3, _h0, _h1, _h2, _h3, _h4, h5, _h6, _h7, p2_5, p3_5, p4_5, p5_5, _p6_5, _p7_5] at he
  nlinarith [he]

private theorem cell_ha5 (A : PowerSeries ℤ) (_h0 : coeff 0 h = 0) (_h1 : coeff 1 h = 0) (hA : A * A = A.subst h) (hh0 : constantCoeff h = 0) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (_h2 : coeff 2 h = 1) (_h3 : coeff 3 h = 2) (_h4 : coeff 4 h = 8) (_h5 : coeff 5 h = 24) (h6 : coeff 6 h = 80) (p2_6 : coeff 6 (h ^ 2) = 20) (p3_6 : coeff 6 (h ^ 3) = 1) (p4_6 : coeff 6 (h ^ 4) = 0) (p5_6 : coeff 6 (h ^ 5) = 0) (p6_6 : coeff 6 (h ^ 6) = 0) (_p7_6 : coeff 6 (h ^ 7) = 0) (_h7 : coeff 7 h = 256) (ha2 : coeff 2 A = 1) (ha3 : coeff 3 A = 4) (ha4 : coeff 4 A = 10) : coeff 5 A = 34 := by
  have he := congrArg (coeff 6) hA
  norm_num [coeff_mul_range, coeff_subst_range _ _ hh0, Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4, _h0, _h1, _h2, _h3, _h4, _h5, h6, _h7, p2_6, p3_6, p4_6, p5_6, p6_6, _p7_6] at he
  nlinarith [he]

private theorem cell_ha6 (A : PowerSeries ℤ) (_h0 : coeff 0 h = 0) (_h1 : coeff 1 h = 0) (hA : A * A = A.subst h) (hh0 : constantCoeff h = 0) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (_h2 : coeff 2 h = 1) (_h3 : coeff 3 h = 2) (_h4 : coeff 4 h = 8) (_h5 : coeff 5 h = 24) (_h6 : coeff 6 h = 80) (h7 : coeff 7 h = 256) (p2_7 : coeff 7 (h ^ 2) = 80) (p3_7 : coeff 7 (h ^ 3) = 6) (p4_7 : coeff 7 (h ^ 4) = 0) (p5_7 : coeff 7 (h ^ 5) = 0) (p6_7 : coeff 7 (h ^ 6) = 0) (p7_7 : coeff 7 (h ^ 7) = 0) (ha2 : coeff 2 A = 1) (ha3 : coeff 3 A = 4) (ha4 : coeff 4 A = 10) (ha5 : coeff 5 A = 34) : coeff 6 A = 106 := by
  have he := congrArg (coeff 7) hA
  norm_num [coeff_mul_range, coeff_subst_range _ _ hh0, Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4, ha5, _h0, _h1, _h2, _h3, _h4, _h5, _h6, h7, p2_7, p3_7, p4_7, p5_7, p6_7, p7_7] at he
  nlinarith [he]

theorem check_DATA_A274479 : DATA_A274479 := by
  intro A h0 h1 hA
  change A ^ 2 = A.subst h at hA
  rw [show A ^ 2 = A * A by ring] at hA
  have hh0 : constantCoeff h = 0 := cell_hh0
  have hDE : D * E = 1 := cell_hDE
  have ha0 : coeff 0 A = 0 := cell_ha0 A h0
  have ha1 : coeff 1 A = 1 := cell_ha1 A h1
  have e0 : coeff 0 E = 1 := cell_e0 hDE
  have h0 : coeff 0 h = 0 := cell_h0 e0
  have p2_0 : coeff 0 (h ^ 2) = 0 := cell_p2_0 h0
  have p3_0 : coeff 0 (h ^ 3) = 0 := cell_p3_0 h0 p2_0
  have p4_0 : coeff 0 (h ^ 4) = 0 := cell_p4_0 h0 p3_0
  have p5_0 : coeff 0 (h ^ 5) = 0 := cell_p5_0 h0 p4_0
  have p6_0 : coeff 0 (h ^ 6) = 0 := cell_p6_0 h0 p5_0
  have p7_0 : coeff 0 (h ^ 7) = 0 := cell_p7_0 h0 p6_0
  have e1 : coeff 1 E = 2 := cell_e1 hDE e0
  have h1 : coeff 1 h = 0 := cell_h1 e0 e1
  have p2_1 : coeff 1 (h ^ 2) = 0 := cell_p2_1 h0 h1
  have p3_1 : coeff 1 (h ^ 3) = 0 := cell_p3_1 h0 h1 p2_0 p2_1
  have p4_1 : coeff 1 (h ^ 4) = 0 := cell_p4_1 h0 h1 p3_0 p3_1
  have p5_1 : coeff 1 (h ^ 5) = 0 := cell_p5_1 h0 h1 p4_0 p4_1
  have p6_1 : coeff 1 (h ^ 6) = 0 := cell_p6_1 h0 h1 p5_0 p5_1
  have p7_1 : coeff 1 (h ^ 7) = 0 := cell_p7_1 h0 h1 p6_0 p6_1
  have e2 : coeff 2 E = 8 := cell_e2 hDE e0 e1
  have h2 : coeff 2 h = 1 := cell_h2 e0 e1 e2
  have p2_2 : coeff 2 (h ^ 2) = 0 := cell_p2_2 h0 h1 h2
  have p3_2 : coeff 2 (h ^ 3) = 0 := cell_p3_2 h0 h1 p2_0 p2_1 h2 p2_2
  have p4_2 : coeff 2 (h ^ 4) = 0 := cell_p4_2 h0 h1 p3_0 p3_1 h2 p3_2
  have p5_2 : coeff 2 (h ^ 5) = 0 := cell_p5_2 h0 h1 p4_0 p4_1 h2 p4_2
  have p6_2 : coeff 2 (h ^ 6) = 0 := cell_p6_2 h0 h1 p5_0 p5_1 h2 p5_2
  have p7_2 : coeff 2 (h ^ 7) = 0 := cell_p7_2 h0 h1 p6_0 p6_1 h2 p6_2
  have e3 : coeff 3 E = 24 := cell_e3 hDE e0 e1 e2
  have h3 : coeff 3 h = 2 := cell_h3 e0 e1 e2 e3
  have p2_3 : coeff 3 (h ^ 2) = 0 := cell_p2_3 h0 h1 h2 h3
  have p3_3 : coeff 3 (h ^ 3) = 0 := cell_p3_3 h0 h1 p2_0 p2_1 h2 p2_2 h3 p2_3
  have p4_3 : coeff 3 (h ^ 4) = 0 := cell_p4_3 h0 h1 p3_0 p3_1 h2 p3_2 h3 p3_3
  have p5_3 : coeff 3 (h ^ 5) = 0 := cell_p5_3 h0 h1 p4_0 p4_1 h2 p4_2 h3 p4_3
  have p6_3 : coeff 3 (h ^ 6) = 0 := cell_p6_3 h0 h1 p5_0 p5_1 h2 p5_2 h3 p5_3
  have p7_3 : coeff 3 (h ^ 7) = 0 := cell_p7_3 h0 h1 p6_0 p6_1 h2 p6_2 h3 p6_3
  have e4 : coeff 4 E = 80 := cell_e4 hDE e0 e1 e2 e3
  have h4 : coeff 4 h = 8 := cell_h4 e0 e1 e2 e3 e4
  have p2_4 : coeff 4 (h ^ 2) = 1 := cell_p2_4 h0 h1 h2 h3 h4
  have p3_4 : coeff 4 (h ^ 3) = 0 := cell_p3_4 h0 h1 p2_0 p2_1 h2 p2_2 h3 p2_3 h4 p2_4
  have p4_4 : coeff 4 (h ^ 4) = 0 := cell_p4_4 h0 h1 p3_0 p3_1 h2 p3_2 h3 p3_3 h4 p3_4
  have p5_4 : coeff 4 (h ^ 5) = 0 := cell_p5_4 h0 h1 p4_0 p4_1 h2 p4_2 h3 p4_3 h4 p4_4
  have p6_4 : coeff 4 (h ^ 6) = 0 := cell_p6_4 h0 h1 p5_0 p5_1 h2 p5_2 h3 p5_3 h4 p5_4
  have p7_4 : coeff 4 (h ^ 7) = 0 := cell_p7_4 h0 h1 p6_0 p6_1 h2 p6_2 h3 p6_3 h4 p6_4
  have e5 : coeff 5 E = 256 := cell_e5 hDE e0 e1 e2 e3 e4
  have h5 : coeff 5 h = 24 := cell_h5 e0 e1 e2 e3 e4 e5
  have p2_5 : coeff 5 (h ^ 2) = 4 := cell_p2_5 h0 h1 h2 h3 h4 h5
  have p3_5 : coeff 5 (h ^ 3) = 0 := cell_p3_5 h0 h1 p2_0 p2_1 h2 p2_2 h3 p2_3 h4 p2_4 h5 p2_5
  have p4_5 : coeff 5 (h ^ 4) = 0 := cell_p4_5 h0 h1 p3_0 p3_1 h2 p3_2 h3 p3_3 h4 p3_4 h5 p3_5
  have p5_5 : coeff 5 (h ^ 5) = 0 := cell_p5_5 h0 h1 p4_0 p4_1 h2 p4_2 h3 p4_3 h4 p4_4 h5 p4_5
  have p6_5 : coeff 5 (h ^ 6) = 0 := cell_p6_5 h0 h1 p5_0 p5_1 h2 p5_2 h3 p5_3 h4 p5_4 h5 p5_5
  have p7_5 : coeff 5 (h ^ 7) = 0 := cell_p7_5 h0 h1 p6_0 p6_1 h2 p6_2 h3 p6_3 h4 p6_4 h5 p6_5
  have e6 : coeff 6 E = 832 := cell_e6 hDE e0 e1 e2 e3 e4 e5
  have h6 : coeff 6 h = 80 := cell_h6 e0 e1 e2 e3 e4 e5 e6
  have p2_6 : coeff 6 (h ^ 2) = 20 := cell_p2_6 h0 h1 h2 h3 h4 h5 h6
  have p3_6 : coeff 6 (h ^ 3) = 1 := cell_p3_6 h0 h1 p2_0 p2_1 h2 p2_2 h3 p2_3 h4 p2_4 h5 p2_5 h6 p2_6
  have p4_6 : coeff 6 (h ^ 4) = 0 := cell_p4_6 h0 h1 p3_0 p3_1 h2 p3_2 h3 p3_3 h4 p3_4 h5 p3_5 h6 p3_6
  have p5_6 : coeff 6 (h ^ 5) = 0 := cell_p5_6 h0 h1 p4_0 p4_1 h2 p4_2 h3 p4_3 h4 p4_4 h5 p4_5 h6 p4_6
  have p6_6 : coeff 6 (h ^ 6) = 0 := cell_p6_6 h0 h1 p5_0 p5_1 h2 p5_2 h3 p5_3 h4 p5_4 h5 p5_5 h6 p5_6
  have p7_6 : coeff 6 (h ^ 7) = 0 := cell_p7_6 h0 h1 p6_0 p6_1 h2 p6_2 h3 p6_3 h4 p6_4 h5 p6_5 h6 p6_6
  have e7 : coeff 7 E = 2688 := cell_e7 hDE e0 e1 e2 e3 e4 e5 e6
  have h7 : coeff 7 h = 256 := cell_h7 e0 e1 e2 e3 e4 e5 e6 e7
  have p2_7 : coeff 7 (h ^ 2) = 80 := cell_p2_7 h0 h1 h2 h3 h4 h5 h6 h7
  have p3_7 : coeff 7 (h ^ 3) = 6 := cell_p3_7 h0 h1 p2_0 p2_1 h2 p2_2 h3 p2_3 h4 p2_4 h5 p2_5 h6 p2_6 h7 p2_7
  have p4_7 : coeff 7 (h ^ 4) = 0 := cell_p4_7 h0 h1 p3_0 p3_1 h2 p3_2 h3 p3_3 h4 p3_4 h5 p3_5 h6 p3_6 h7 p3_7
  have p5_7 : coeff 7 (h ^ 5) = 0 := cell_p5_7 h0 h1 p4_0 p4_1 h2 p4_2 h3 p4_3 h4 p4_4 h5 p4_5 h6 p4_6 h7 p4_7
  have p6_7 : coeff 7 (h ^ 6) = 0 := cell_p6_7 h0 h1 p5_0 p5_1 h2 p5_2 h3 p5_3 h4 p5_4 h5 p5_5 h6 p5_6 h7 p5_7
  have p7_7 : coeff 7 (h ^ 7) = 0 := cell_p7_7 h0 h1 p6_0 p6_1 h2 p6_2 h3 p6_3 h4 p6_4 h5 p6_5 h6 p6_6 h7 p6_7
  have ha2 : coeff 2 A = 1 := cell_ha2 A h0 h1 hA hh0 ha0 ha1 h2 h3 p2_3 p3_3 p4_3 p5_3 p6_3 p7_3 h4 h5 h6 h7
  have ha3 : coeff 3 A = 4 := cell_ha3 A h0 h1 hA hh0 ha0 ha1 h2 h3 h4 p2_4 p3_4 p4_4 p5_4 p6_4 p7_4 h5 h6 h7 ha2
  have ha4 : coeff 4 A = 10 := cell_ha4 A h0 h1 hA hh0 ha0 ha1 h2 h3 h4 h5 p2_5 p3_5 p4_5 p5_5 p6_5 p7_5 h6 h7 ha2 ha3
  have ha5 : coeff 5 A = 34 := cell_ha5 A h0 h1 hA hh0 ha0 ha1 h2 h3 h4 h5 h6 p2_6 p3_6 p4_6 p5_6 p6_6 p7_6 h7 ha2 ha3 ha4
  have ha6 : coeff 6 A = 106 := cell_ha6 A h0 h1 hA hh0 ha0 ha1 h2 h3 h4 h5 h6 h7 p2_7 p3_7 p4_7 p5_7 p6_7 p7_7 ha2 ha3 ha4 ha5
  exact ⟨ha2, ha3, ha4, ha5, ha6⟩

end BackfillPaper2.DataRational274479
#print axioms BackfillPaper2.DataRational274479.check_DATA_A274479
