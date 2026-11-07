import Research.Backfill.Paper2.FiniteCoefficients

/-! Every finite table cell is proved from exact convolution. No table is a premise. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.DataSelf107099
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.FiniteCoefficients

private theorem cell_ha0 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0) : coeff 0 A = 0 := by
  exact by simpa only [coeff_zero_eq_constantCoeff_apply] using h0

private theorem cell_ha1 (A : PowerSeries ℤ) (h1 : coeff 1 A = 1) : coeff 1 A = 1 := by
  exact h1

private theorem cell_p2_0 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) : coeff 0 (A ^ 2) = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0]

private theorem cell_p3_0 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (_p2_0 : coeff 0 (A ^ 2) = 0) : coeff 0 (A ^ 3) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, _p2_0]

private theorem cell_p4_0 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (_p3_0 : coeff 0 (A ^ 3) = 0) : coeff 0 (A ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, _p3_0]

private theorem cell_p5_0 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (_p4_0 : coeff 0 (A ^ 4) = 0) : coeff 0 (A ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, _p4_0]

private theorem cell_p6_0 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (_p5_0 : coeff 0 (A ^ 5) = 0) : coeff 0 (A ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, _p5_0]

private theorem cell_p7_0 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (_p6_0 : coeff 0 (A ^ 6) = 0) : coeff 0 (A ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, _p6_0]

private theorem cell_p8_0 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (_p7_0 : coeff 0 (A ^ 7) = 0) : coeff 0 (A ^ 8) = 0 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, _p7_0]

private theorem cell_p9_0 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (_p8_0 : coeff 0 (A ^ 8) = 0) : coeff 0 (A ^ 9) = 0 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, _p8_0]

private theorem cell_p2_1 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) : coeff 1 (A ^ 2) = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1]

private theorem cell_p3_1 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p2_0 : coeff 0 (A ^ 2) = 0) (p2_1 : coeff 1 (A ^ 2) = 0) : coeff 1 (A ^ 3) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0, p2_1]

private theorem cell_p4_1 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p3_0 : coeff 0 (A ^ 3) = 0) (p3_1 : coeff 1 (A ^ 3) = 0) : coeff 1 (A ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p3_0, p3_1]

private theorem cell_p5_1 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p4_0 : coeff 0 (A ^ 4) = 0) (p4_1 : coeff 1 (A ^ 4) = 0) : coeff 1 (A ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p4_0, p4_1]

private theorem cell_p6_1 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p5_0 : coeff 0 (A ^ 5) = 0) (p5_1 : coeff 1 (A ^ 5) = 0) : coeff 1 (A ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p5_0, p5_1]

private theorem cell_p7_1 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p6_0 : coeff 0 (A ^ 6) = 0) (p6_1 : coeff 1 (A ^ 6) = 0) : coeff 1 (A ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p6_0, p6_1]

private theorem cell_p8_1 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p7_0 : coeff 0 (A ^ 7) = 0) (p7_1 : coeff 1 (A ^ 7) = 0) : coeff 1 (A ^ 8) = 0 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p7_0, p7_1]

private theorem cell_p9_1 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p8_0 : coeff 0 (A ^ 8) = 0) (p8_1 : coeff 1 (A ^ 8) = 0) : coeff 1 (A ^ 9) = 0 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p8_0, p8_1]

private theorem cell_p2_2 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) : coeff 2 (A ^ 2) = 1 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1]

private theorem cell_p3_2 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p2_0 : coeff 0 (A ^ 2) = 0) (p2_1 : coeff 1 (A ^ 2) = 0) (p2_2 : coeff 2 (A ^ 2) = 1) : coeff 2 (A ^ 3) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0, p2_1, p2_2]

private theorem cell_p4_2 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p3_0 : coeff 0 (A ^ 3) = 0) (p3_1 : coeff 1 (A ^ 3) = 0) (p3_2 : coeff 2 (A ^ 3) = 0) : coeff 2 (A ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p3_0, p3_1, p3_2]

private theorem cell_p5_2 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p4_0 : coeff 0 (A ^ 4) = 0) (p4_1 : coeff 1 (A ^ 4) = 0) (p4_2 : coeff 2 (A ^ 4) = 0) : coeff 2 (A ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p4_0, p4_1, p4_2]

private theorem cell_p6_2 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p5_0 : coeff 0 (A ^ 5) = 0) (p5_1 : coeff 1 (A ^ 5) = 0) (p5_2 : coeff 2 (A ^ 5) = 0) : coeff 2 (A ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p5_0, p5_1, p5_2]

private theorem cell_p7_2 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p6_0 : coeff 0 (A ^ 6) = 0) (p6_1 : coeff 1 (A ^ 6) = 0) (p6_2 : coeff 2 (A ^ 6) = 0) : coeff 2 (A ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p6_0, p6_1, p6_2]

private theorem cell_p8_2 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p7_0 : coeff 0 (A ^ 7) = 0) (p7_1 : coeff 1 (A ^ 7) = 0) (p7_2 : coeff 2 (A ^ 7) = 0) : coeff 2 (A ^ 8) = 0 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p7_0, p7_1, p7_2]

private theorem cell_p9_2 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p8_0 : coeff 0 (A ^ 8) = 0) (p8_1 : coeff 1 (A ^ 8) = 0) (p8_2 : coeff 2 (A ^ 8) = 0) : coeff 2 (A ^ 9) = 0 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p8_0, p8_1, p8_2]

private theorem cell_ha2 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0) (hA : A.subst A = X + 4 * X ^ 3) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p2_2 : coeff 2 (A ^ 2) = 1) (_p3_2 : coeff 2 (A ^ 3) = 0) (_p4_2 : coeff 2 (A ^ 4) = 0) (_p5_2 : coeff 2 (A ^ 5) = 0) (_p6_2 : coeff 2 (A ^ 6) = 0) (_p7_2 : coeff 2 (A ^ 7) = 0) (_p8_2 : coeff 2 (A ^ 8) = 0) (_p9_2 : coeff 2 (A ^ 9) = 0) : coeff 2 A = 0 := by
  have he := congrArg (coeff 2) hA
  norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, coeff_X, coeff_X_pow, ha0, ha1, p2_2, _p3_2, _p4_2, _p5_2, _p6_2, _p7_2, _p8_2, _p9_2] at he
  omega

private theorem cell_p2_3 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 0) : coeff 3 (A ^ 2) = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2]

private theorem cell_p3_3 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p2_0 : coeff 0 (A ^ 2) = 0) (p2_1 : coeff 1 (A ^ 2) = 0) (p2_2 : coeff 2 (A ^ 2) = 1) (ha2 : coeff 2 A = 0) (p2_3 : coeff 3 (A ^ 2) = 0) : coeff 3 (A ^ 3) = 1 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p2_0, p2_1, p2_2, p2_3]

private theorem cell_p4_3 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p3_0 : coeff 0 (A ^ 3) = 0) (p3_1 : coeff 1 (A ^ 3) = 0) (p3_2 : coeff 2 (A ^ 3) = 0) (ha2 : coeff 2 A = 0) (p3_3 : coeff 3 (A ^ 3) = 1) : coeff 3 (A ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p3_0, p3_1, p3_2, p3_3]

private theorem cell_p5_3 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p4_0 : coeff 0 (A ^ 4) = 0) (p4_1 : coeff 1 (A ^ 4) = 0) (p4_2 : coeff 2 (A ^ 4) = 0) (ha2 : coeff 2 A = 0) (p4_3 : coeff 3 (A ^ 4) = 0) : coeff 3 (A ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p4_0, p4_1, p4_2, p4_3]

private theorem cell_p6_3 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p5_0 : coeff 0 (A ^ 5) = 0) (p5_1 : coeff 1 (A ^ 5) = 0) (p5_2 : coeff 2 (A ^ 5) = 0) (ha2 : coeff 2 A = 0) (p5_3 : coeff 3 (A ^ 5) = 0) : coeff 3 (A ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p5_0, p5_1, p5_2, p5_3]

private theorem cell_p7_3 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p6_0 : coeff 0 (A ^ 6) = 0) (p6_1 : coeff 1 (A ^ 6) = 0) (p6_2 : coeff 2 (A ^ 6) = 0) (ha2 : coeff 2 A = 0) (p6_3 : coeff 3 (A ^ 6) = 0) : coeff 3 (A ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p6_0, p6_1, p6_2, p6_3]

private theorem cell_p8_3 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p7_0 : coeff 0 (A ^ 7) = 0) (p7_1 : coeff 1 (A ^ 7) = 0) (p7_2 : coeff 2 (A ^ 7) = 0) (ha2 : coeff 2 A = 0) (p7_3 : coeff 3 (A ^ 7) = 0) : coeff 3 (A ^ 8) = 0 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p7_0, p7_1, p7_2, p7_3]

private theorem cell_p9_3 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p8_0 : coeff 0 (A ^ 8) = 0) (p8_1 : coeff 1 (A ^ 8) = 0) (p8_2 : coeff 2 (A ^ 8) = 0) (ha2 : coeff 2 A = 0) (p8_3 : coeff 3 (A ^ 8) = 0) : coeff 3 (A ^ 9) = 0 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p8_0, p8_1, p8_2, p8_3]

private theorem cell_ha3 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0) (hA : A.subst A = X + 4 * X ^ 3) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 0) (p2_3 : coeff 3 (A ^ 2) = 0) (p3_3 : coeff 3 (A ^ 3) = 1) (_p4_3 : coeff 3 (A ^ 4) = 0) (_p5_3 : coeff 3 (A ^ 5) = 0) (_p6_3 : coeff 3 (A ^ 6) = 0) (_p7_3 : coeff 3 (A ^ 7) = 0) (_p8_3 : coeff 3 (A ^ 8) = 0) (_p9_3 : coeff 3 (A ^ 9) = 0) : coeff 3 A = 2 := by
  have he := congrArg (coeff 3) hA
  norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, coeff_X, coeff_X_pow, ha0, ha1, ha2, p2_3, p3_3, _p4_3, _p5_3, _p6_3, _p7_3, _p8_3, _p9_3] at he
  omega

private theorem cell_p2_4 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 0) (ha3 : coeff 3 A = 2) : coeff 4 (A ^ 2) = 4 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3]

private theorem cell_p3_4 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p2_0 : coeff 0 (A ^ 2) = 0) (p2_1 : coeff 1 (A ^ 2) = 0) (p2_2 : coeff 2 (A ^ 2) = 1) (ha2 : coeff 2 A = 0) (p2_3 : coeff 3 (A ^ 2) = 0) (ha3 : coeff 3 A = 2) (p2_4 : coeff 4 (A ^ 2) = 4) : coeff 4 (A ^ 3) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p2_0, p2_1, p2_2, p2_3, p2_4]

private theorem cell_p4_4 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p3_0 : coeff 0 (A ^ 3) = 0) (p3_1 : coeff 1 (A ^ 3) = 0) (p3_2 : coeff 2 (A ^ 3) = 0) (ha2 : coeff 2 A = 0) (p3_3 : coeff 3 (A ^ 3) = 1) (ha3 : coeff 3 A = 2) (p3_4 : coeff 4 (A ^ 3) = 0) : coeff 4 (A ^ 4) = 1 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p3_0, p3_1, p3_2, p3_3, p3_4]

private theorem cell_p5_4 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p4_0 : coeff 0 (A ^ 4) = 0) (p4_1 : coeff 1 (A ^ 4) = 0) (p4_2 : coeff 2 (A ^ 4) = 0) (ha2 : coeff 2 A = 0) (p4_3 : coeff 3 (A ^ 4) = 0) (ha3 : coeff 3 A = 2) (p4_4 : coeff 4 (A ^ 4) = 1) : coeff 4 (A ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p4_0, p4_1, p4_2, p4_3, p4_4]

private theorem cell_p6_4 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p5_0 : coeff 0 (A ^ 5) = 0) (p5_1 : coeff 1 (A ^ 5) = 0) (p5_2 : coeff 2 (A ^ 5) = 0) (ha2 : coeff 2 A = 0) (p5_3 : coeff 3 (A ^ 5) = 0) (ha3 : coeff 3 A = 2) (p5_4 : coeff 4 (A ^ 5) = 0) : coeff 4 (A ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p5_0, p5_1, p5_2, p5_3, p5_4]

private theorem cell_p7_4 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p6_0 : coeff 0 (A ^ 6) = 0) (p6_1 : coeff 1 (A ^ 6) = 0) (p6_2 : coeff 2 (A ^ 6) = 0) (ha2 : coeff 2 A = 0) (p6_3 : coeff 3 (A ^ 6) = 0) (ha3 : coeff 3 A = 2) (p6_4 : coeff 4 (A ^ 6) = 0) : coeff 4 (A ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p6_0, p6_1, p6_2, p6_3, p6_4]

private theorem cell_p8_4 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p7_0 : coeff 0 (A ^ 7) = 0) (p7_1 : coeff 1 (A ^ 7) = 0) (p7_2 : coeff 2 (A ^ 7) = 0) (ha2 : coeff 2 A = 0) (p7_3 : coeff 3 (A ^ 7) = 0) (ha3 : coeff 3 A = 2) (p7_4 : coeff 4 (A ^ 7) = 0) : coeff 4 (A ^ 8) = 0 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p7_0, p7_1, p7_2, p7_3, p7_4]

private theorem cell_p9_4 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p8_0 : coeff 0 (A ^ 8) = 0) (p8_1 : coeff 1 (A ^ 8) = 0) (p8_2 : coeff 2 (A ^ 8) = 0) (ha2 : coeff 2 A = 0) (p8_3 : coeff 3 (A ^ 8) = 0) (ha3 : coeff 3 A = 2) (p8_4 : coeff 4 (A ^ 8) = 0) : coeff 4 (A ^ 9) = 0 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p8_0, p8_1, p8_2, p8_3, p8_4]

private theorem cell_ha4 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0) (hA : A.subst A = X + 4 * X ^ 3) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 0) (ha3 : coeff 3 A = 2) (p2_4 : coeff 4 (A ^ 2) = 4) (p3_4 : coeff 4 (A ^ 3) = 0) (p4_4 : coeff 4 (A ^ 4) = 1) (_p5_4 : coeff 4 (A ^ 5) = 0) (_p6_4 : coeff 4 (A ^ 6) = 0) (_p7_4 : coeff 4 (A ^ 7) = 0) (_p8_4 : coeff 4 (A ^ 8) = 0) (_p9_4 : coeff 4 (A ^ 9) = 0) : coeff 4 A = 0 := by
  have he := congrArg (coeff 4) hA
  norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, coeff_X, coeff_X_pow, ha0, ha1, ha2, ha3, p2_4, p3_4, p4_4, _p5_4, _p6_4, _p7_4, _p8_4, _p9_4] at he
  omega

private theorem cell_p2_5 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 0) (ha3 : coeff 3 A = 2) (ha4 : coeff 4 A = 0) : coeff 5 (A ^ 2) = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4]

private theorem cell_p3_5 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p2_0 : coeff 0 (A ^ 2) = 0) (p2_1 : coeff 1 (A ^ 2) = 0) (p2_2 : coeff 2 (A ^ 2) = 1) (ha2 : coeff 2 A = 0) (p2_3 : coeff 3 (A ^ 2) = 0) (ha3 : coeff 3 A = 2) (p2_4 : coeff 4 (A ^ 2) = 4) (ha4 : coeff 4 A = 0) (p2_5 : coeff 5 (A ^ 2) = 0) : coeff 5 (A ^ 3) = 6 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p2_0, p2_1, p2_2, p2_3, p2_4, p2_5]

private theorem cell_p4_5 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p3_0 : coeff 0 (A ^ 3) = 0) (p3_1 : coeff 1 (A ^ 3) = 0) (p3_2 : coeff 2 (A ^ 3) = 0) (ha2 : coeff 2 A = 0) (p3_3 : coeff 3 (A ^ 3) = 1) (ha3 : coeff 3 A = 2) (p3_4 : coeff 4 (A ^ 3) = 0) (ha4 : coeff 4 A = 0) (p3_5 : coeff 5 (A ^ 3) = 6) : coeff 5 (A ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p3_0, p3_1, p3_2, p3_3, p3_4, p3_5]

private theorem cell_p5_5 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p4_0 : coeff 0 (A ^ 4) = 0) (p4_1 : coeff 1 (A ^ 4) = 0) (p4_2 : coeff 2 (A ^ 4) = 0) (ha2 : coeff 2 A = 0) (p4_3 : coeff 3 (A ^ 4) = 0) (ha3 : coeff 3 A = 2) (p4_4 : coeff 4 (A ^ 4) = 1) (ha4 : coeff 4 A = 0) (p4_5 : coeff 5 (A ^ 4) = 0) : coeff 5 (A ^ 5) = 1 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p4_0, p4_1, p4_2, p4_3, p4_4, p4_5]

private theorem cell_p6_5 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p5_0 : coeff 0 (A ^ 5) = 0) (p5_1 : coeff 1 (A ^ 5) = 0) (p5_2 : coeff 2 (A ^ 5) = 0) (ha2 : coeff 2 A = 0) (p5_3 : coeff 3 (A ^ 5) = 0) (ha3 : coeff 3 A = 2) (p5_4 : coeff 4 (A ^ 5) = 0) (ha4 : coeff 4 A = 0) (p5_5 : coeff 5 (A ^ 5) = 1) : coeff 5 (A ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p5_0, p5_1, p5_2, p5_3, p5_4, p5_5]

private theorem cell_p7_5 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p6_0 : coeff 0 (A ^ 6) = 0) (p6_1 : coeff 1 (A ^ 6) = 0) (p6_2 : coeff 2 (A ^ 6) = 0) (ha2 : coeff 2 A = 0) (p6_3 : coeff 3 (A ^ 6) = 0) (ha3 : coeff 3 A = 2) (p6_4 : coeff 4 (A ^ 6) = 0) (ha4 : coeff 4 A = 0) (p6_5 : coeff 5 (A ^ 6) = 0) : coeff 5 (A ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p6_0, p6_1, p6_2, p6_3, p6_4, p6_5]

private theorem cell_p8_5 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p7_0 : coeff 0 (A ^ 7) = 0) (p7_1 : coeff 1 (A ^ 7) = 0) (p7_2 : coeff 2 (A ^ 7) = 0) (ha2 : coeff 2 A = 0) (p7_3 : coeff 3 (A ^ 7) = 0) (ha3 : coeff 3 A = 2) (p7_4 : coeff 4 (A ^ 7) = 0) (ha4 : coeff 4 A = 0) (p7_5 : coeff 5 (A ^ 7) = 0) : coeff 5 (A ^ 8) = 0 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p7_0, p7_1, p7_2, p7_3, p7_4, p7_5]

private theorem cell_p9_5 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p8_0 : coeff 0 (A ^ 8) = 0) (p8_1 : coeff 1 (A ^ 8) = 0) (p8_2 : coeff 2 (A ^ 8) = 0) (ha2 : coeff 2 A = 0) (p8_3 : coeff 3 (A ^ 8) = 0) (ha3 : coeff 3 A = 2) (p8_4 : coeff 4 (A ^ 8) = 0) (ha4 : coeff 4 A = 0) (p8_5 : coeff 5 (A ^ 8) = 0) : coeff 5 (A ^ 9) = 0 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p8_0, p8_1, p8_2, p8_3, p8_4, p8_5]

private theorem cell_ha5 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0) (hA : A.subst A = X + 4 * X ^ 3) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 0) (ha3 : coeff 3 A = 2) (ha4 : coeff 4 A = 0) (p2_5 : coeff 5 (A ^ 2) = 0) (p3_5 : coeff 5 (A ^ 3) = 6) (p4_5 : coeff 5 (A ^ 4) = 0) (p5_5 : coeff 5 (A ^ 5) = 1) (_p6_5 : coeff 5 (A ^ 6) = 0) (_p7_5 : coeff 5 (A ^ 7) = 0) (_p8_5 : coeff 5 (A ^ 8) = 0) (_p9_5 : coeff 5 (A ^ 9) = 0) : coeff 5 A = -6 := by
  have he := congrArg (coeff 5) hA
  norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, coeff_X, coeff_X_pow, ha0, ha1, ha2, ha3, ha4, p2_5, p3_5, p4_5, p5_5, _p6_5, _p7_5, _p8_5, _p9_5] at he
  omega

private theorem cell_p2_6 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 0) (ha3 : coeff 3 A = 2) (ha4 : coeff 4 A = 0) (ha5 : coeff 5 A = -6) : coeff 6 (A ^ 2) = -8 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5]

private theorem cell_p3_6 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p2_0 : coeff 0 (A ^ 2) = 0) (p2_1 : coeff 1 (A ^ 2) = 0) (p2_2 : coeff 2 (A ^ 2) = 1) (ha2 : coeff 2 A = 0) (p2_3 : coeff 3 (A ^ 2) = 0) (ha3 : coeff 3 A = 2) (p2_4 : coeff 4 (A ^ 2) = 4) (ha4 : coeff 4 A = 0) (p2_5 : coeff 5 (A ^ 2) = 0) (ha5 : coeff 5 A = -6) (p2_6 : coeff 6 (A ^ 2) = -8) : coeff 6 (A ^ 3) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6]

private theorem cell_p4_6 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p3_0 : coeff 0 (A ^ 3) = 0) (p3_1 : coeff 1 (A ^ 3) = 0) (p3_2 : coeff 2 (A ^ 3) = 0) (ha2 : coeff 2 A = 0) (p3_3 : coeff 3 (A ^ 3) = 1) (ha3 : coeff 3 A = 2) (p3_4 : coeff 4 (A ^ 3) = 0) (ha4 : coeff 4 A = 0) (p3_5 : coeff 5 (A ^ 3) = 6) (ha5 : coeff 5 A = -6) (p3_6 : coeff 6 (A ^ 3) = 0) : coeff 6 (A ^ 4) = 8 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6]

private theorem cell_p5_6 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p4_0 : coeff 0 (A ^ 4) = 0) (p4_1 : coeff 1 (A ^ 4) = 0) (p4_2 : coeff 2 (A ^ 4) = 0) (ha2 : coeff 2 A = 0) (p4_3 : coeff 3 (A ^ 4) = 0) (ha3 : coeff 3 A = 2) (p4_4 : coeff 4 (A ^ 4) = 1) (ha4 : coeff 4 A = 0) (p4_5 : coeff 5 (A ^ 4) = 0) (ha5 : coeff 5 A = -6) (p4_6 : coeff 6 (A ^ 4) = 8) : coeff 6 (A ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6]

private theorem cell_p6_6 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p5_0 : coeff 0 (A ^ 5) = 0) (p5_1 : coeff 1 (A ^ 5) = 0) (p5_2 : coeff 2 (A ^ 5) = 0) (ha2 : coeff 2 A = 0) (p5_3 : coeff 3 (A ^ 5) = 0) (ha3 : coeff 3 A = 2) (p5_4 : coeff 4 (A ^ 5) = 0) (ha4 : coeff 4 A = 0) (p5_5 : coeff 5 (A ^ 5) = 1) (ha5 : coeff 5 A = -6) (p5_6 : coeff 6 (A ^ 5) = 0) : coeff 6 (A ^ 6) = 1 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, p5_0, p5_1, p5_2, p5_3, p5_4, p5_5, p5_6]

private theorem cell_p7_6 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p6_0 : coeff 0 (A ^ 6) = 0) (p6_1 : coeff 1 (A ^ 6) = 0) (p6_2 : coeff 2 (A ^ 6) = 0) (ha2 : coeff 2 A = 0) (p6_3 : coeff 3 (A ^ 6) = 0) (ha3 : coeff 3 A = 2) (p6_4 : coeff 4 (A ^ 6) = 0) (ha4 : coeff 4 A = 0) (p6_5 : coeff 5 (A ^ 6) = 0) (ha5 : coeff 5 A = -6) (p6_6 : coeff 6 (A ^ 6) = 1) : coeff 6 (A ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, p6_0, p6_1, p6_2, p6_3, p6_4, p6_5, p6_6]

private theorem cell_p8_6 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p7_0 : coeff 0 (A ^ 7) = 0) (p7_1 : coeff 1 (A ^ 7) = 0) (p7_2 : coeff 2 (A ^ 7) = 0) (ha2 : coeff 2 A = 0) (p7_3 : coeff 3 (A ^ 7) = 0) (ha3 : coeff 3 A = 2) (p7_4 : coeff 4 (A ^ 7) = 0) (ha4 : coeff 4 A = 0) (p7_5 : coeff 5 (A ^ 7) = 0) (ha5 : coeff 5 A = -6) (p7_6 : coeff 6 (A ^ 7) = 0) : coeff 6 (A ^ 8) = 0 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, p7_0, p7_1, p7_2, p7_3, p7_4, p7_5, p7_6]

private theorem cell_p9_6 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p8_0 : coeff 0 (A ^ 8) = 0) (p8_1 : coeff 1 (A ^ 8) = 0) (p8_2 : coeff 2 (A ^ 8) = 0) (ha2 : coeff 2 A = 0) (p8_3 : coeff 3 (A ^ 8) = 0) (ha3 : coeff 3 A = 2) (p8_4 : coeff 4 (A ^ 8) = 0) (ha4 : coeff 4 A = 0) (p8_5 : coeff 5 (A ^ 8) = 0) (ha5 : coeff 5 A = -6) (p8_6 : coeff 6 (A ^ 8) = 0) : coeff 6 (A ^ 9) = 0 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, p8_0, p8_1, p8_2, p8_3, p8_4, p8_5, p8_6]

private theorem cell_ha6 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0) (hA : A.subst A = X + 4 * X ^ 3) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 0) (ha3 : coeff 3 A = 2) (ha4 : coeff 4 A = 0) (ha5 : coeff 5 A = -6) (p2_6 : coeff 6 (A ^ 2) = -8) (p3_6 : coeff 6 (A ^ 3) = 0) (p4_6 : coeff 6 (A ^ 4) = 8) (p5_6 : coeff 6 (A ^ 5) = 0) (p6_6 : coeff 6 (A ^ 6) = 1) (_p7_6 : coeff 6 (A ^ 7) = 0) (_p8_6 : coeff 6 (A ^ 8) = 0) (_p9_6 : coeff 6 (A ^ 9) = 0) : coeff 6 A = 0 := by
  have he := congrArg (coeff 6) hA
  norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, coeff_X, coeff_X_pow, ha0, ha1, ha2, ha3, ha4, ha5, p2_6, p3_6, p4_6, p5_6, p6_6, _p7_6, _p8_6, _p9_6] at he
  omega

private theorem cell_p2_7 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 0) (ha3 : coeff 3 A = 2) (ha4 : coeff 4 A = 0) (ha5 : coeff 5 A = -6) (ha6 : coeff 6 A = 0) : coeff 7 (A ^ 2) = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6]

private theorem cell_p3_7 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p2_0 : coeff 0 (A ^ 2) = 0) (p2_1 : coeff 1 (A ^ 2) = 0) (p2_2 : coeff 2 (A ^ 2) = 1) (ha2 : coeff 2 A = 0) (p2_3 : coeff 3 (A ^ 2) = 0) (ha3 : coeff 3 A = 2) (p2_4 : coeff 4 (A ^ 2) = 4) (ha4 : coeff 4 A = 0) (p2_5 : coeff 5 (A ^ 2) = 0) (ha5 : coeff 5 A = -6) (p2_6 : coeff 6 (A ^ 2) = -8) (ha6 : coeff 6 A = 0) (p2_7 : coeff 7 (A ^ 2) = 0) : coeff 7 (A ^ 3) = -6 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7]

private theorem cell_p4_7 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p3_0 : coeff 0 (A ^ 3) = 0) (p3_1 : coeff 1 (A ^ 3) = 0) (p3_2 : coeff 2 (A ^ 3) = 0) (ha2 : coeff 2 A = 0) (p3_3 : coeff 3 (A ^ 3) = 1) (ha3 : coeff 3 A = 2) (p3_4 : coeff 4 (A ^ 3) = 0) (ha4 : coeff 4 A = 0) (p3_5 : coeff 5 (A ^ 3) = 6) (ha5 : coeff 5 A = -6) (p3_6 : coeff 6 (A ^ 3) = 0) (ha6 : coeff 6 A = 0) (p3_7 : coeff 7 (A ^ 3) = -6) : coeff 7 (A ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7]

private theorem cell_p5_7 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p4_0 : coeff 0 (A ^ 4) = 0) (p4_1 : coeff 1 (A ^ 4) = 0) (p4_2 : coeff 2 (A ^ 4) = 0) (ha2 : coeff 2 A = 0) (p4_3 : coeff 3 (A ^ 4) = 0) (ha3 : coeff 3 A = 2) (p4_4 : coeff 4 (A ^ 4) = 1) (ha4 : coeff 4 A = 0) (p4_5 : coeff 5 (A ^ 4) = 0) (ha5 : coeff 5 A = -6) (p4_6 : coeff 6 (A ^ 4) = 8) (ha6 : coeff 6 A = 0) (p4_7 : coeff 7 (A ^ 4) = 0) : coeff 7 (A ^ 5) = 10 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7]

private theorem cell_p6_7 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p5_0 : coeff 0 (A ^ 5) = 0) (p5_1 : coeff 1 (A ^ 5) = 0) (p5_2 : coeff 2 (A ^ 5) = 0) (ha2 : coeff 2 A = 0) (p5_3 : coeff 3 (A ^ 5) = 0) (ha3 : coeff 3 A = 2) (p5_4 : coeff 4 (A ^ 5) = 0) (ha4 : coeff 4 A = 0) (p5_5 : coeff 5 (A ^ 5) = 1) (ha5 : coeff 5 A = -6) (p5_6 : coeff 6 (A ^ 5) = 0) (ha6 : coeff 6 A = 0) (p5_7 : coeff 7 (A ^ 5) = 10) : coeff 7 (A ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, p5_0, p5_1, p5_2, p5_3, p5_4, p5_5, p5_6, p5_7]

private theorem cell_p7_7 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p6_0 : coeff 0 (A ^ 6) = 0) (p6_1 : coeff 1 (A ^ 6) = 0) (p6_2 : coeff 2 (A ^ 6) = 0) (ha2 : coeff 2 A = 0) (p6_3 : coeff 3 (A ^ 6) = 0) (ha3 : coeff 3 A = 2) (p6_4 : coeff 4 (A ^ 6) = 0) (ha4 : coeff 4 A = 0) (p6_5 : coeff 5 (A ^ 6) = 0) (ha5 : coeff 5 A = -6) (p6_6 : coeff 6 (A ^ 6) = 1) (ha6 : coeff 6 A = 0) (p6_7 : coeff 7 (A ^ 6) = 0) : coeff 7 (A ^ 7) = 1 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, p6_0, p6_1, p6_2, p6_3, p6_4, p6_5, p6_6, p6_7]

private theorem cell_p8_7 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p7_0 : coeff 0 (A ^ 7) = 0) (p7_1 : coeff 1 (A ^ 7) = 0) (p7_2 : coeff 2 (A ^ 7) = 0) (ha2 : coeff 2 A = 0) (p7_3 : coeff 3 (A ^ 7) = 0) (ha3 : coeff 3 A = 2) (p7_4 : coeff 4 (A ^ 7) = 0) (ha4 : coeff 4 A = 0) (p7_5 : coeff 5 (A ^ 7) = 0) (ha5 : coeff 5 A = -6) (p7_6 : coeff 6 (A ^ 7) = 0) (ha6 : coeff 6 A = 0) (p7_7 : coeff 7 (A ^ 7) = 1) : coeff 7 (A ^ 8) = 0 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, p7_0, p7_1, p7_2, p7_3, p7_4, p7_5, p7_6, p7_7]

private theorem cell_p9_7 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p8_0 : coeff 0 (A ^ 8) = 0) (p8_1 : coeff 1 (A ^ 8) = 0) (p8_2 : coeff 2 (A ^ 8) = 0) (ha2 : coeff 2 A = 0) (p8_3 : coeff 3 (A ^ 8) = 0) (ha3 : coeff 3 A = 2) (p8_4 : coeff 4 (A ^ 8) = 0) (ha4 : coeff 4 A = 0) (p8_5 : coeff 5 (A ^ 8) = 0) (ha5 : coeff 5 A = -6) (p8_6 : coeff 6 (A ^ 8) = 0) (ha6 : coeff 6 A = 0) (p8_7 : coeff 7 (A ^ 8) = 0) : coeff 7 (A ^ 9) = 0 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, p8_0, p8_1, p8_2, p8_3, p8_4, p8_5, p8_6, p8_7]

private theorem cell_ha7 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0) (hA : A.subst A = X + 4 * X ^ 3) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 0) (ha3 : coeff 3 A = 2) (ha4 : coeff 4 A = 0) (ha5 : coeff 5 A = -6) (ha6 : coeff 6 A = 0) (p2_7 : coeff 7 (A ^ 2) = 0) (p3_7 : coeff 7 (A ^ 3) = -6) (p4_7 : coeff 7 (A ^ 4) = 0) (p5_7 : coeff 7 (A ^ 5) = 10) (p6_7 : coeff 7 (A ^ 6) = 0) (p7_7 : coeff 7 (A ^ 7) = 1) (_p8_7 : coeff 7 (A ^ 8) = 0) (_p9_7 : coeff 7 (A ^ 9) = 0) : coeff 7 A = 36 := by
  have he := congrArg (coeff 7) hA
  norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, coeff_X, coeff_X_pow, ha0, ha1, ha2, ha3, ha4, ha5, ha6, p2_7, p3_7, p4_7, p5_7, p6_7, p7_7, _p8_7, _p9_7] at he
  omega

private theorem cell_p2_8 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 0) (ha3 : coeff 3 A = 2) (ha4 : coeff 4 A = 0) (ha5 : coeff 5 A = -6) (ha6 : coeff 6 A = 0) (ha7 : coeff 7 A = 36) : coeff 8 (A ^ 2) = 48 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]

private theorem cell_p3_8 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p2_0 : coeff 0 (A ^ 2) = 0) (p2_1 : coeff 1 (A ^ 2) = 0) (p2_2 : coeff 2 (A ^ 2) = 1) (ha2 : coeff 2 A = 0) (p2_3 : coeff 3 (A ^ 2) = 0) (ha3 : coeff 3 A = 2) (p2_4 : coeff 4 (A ^ 2) = 4) (ha4 : coeff 4 A = 0) (p2_5 : coeff 5 (A ^ 2) = 0) (ha5 : coeff 5 A = -6) (p2_6 : coeff 6 (A ^ 2) = -8) (ha6 : coeff 6 A = 0) (p2_7 : coeff 7 (A ^ 2) = 0) (ha7 : coeff 7 A = 36) (p2_8 : coeff 8 (A ^ 2) = 48) : coeff 8 (A ^ 3) = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8]

private theorem cell_p4_8 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p3_0 : coeff 0 (A ^ 3) = 0) (p3_1 : coeff 1 (A ^ 3) = 0) (p3_2 : coeff 2 (A ^ 3) = 0) (ha2 : coeff 2 A = 0) (p3_3 : coeff 3 (A ^ 3) = 1) (ha3 : coeff 3 A = 2) (p3_4 : coeff 4 (A ^ 3) = 0) (ha4 : coeff 4 A = 0) (p3_5 : coeff 5 (A ^ 3) = 6) (ha5 : coeff 5 A = -6) (p3_6 : coeff 6 (A ^ 3) = 0) (ha6 : coeff 6 A = 0) (p3_7 : coeff 7 (A ^ 3) = -6) (ha7 : coeff 7 A = 36) (p3_8 : coeff 8 (A ^ 3) = 0) : coeff 8 (A ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8]

private theorem cell_p5_8 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p4_0 : coeff 0 (A ^ 4) = 0) (p4_1 : coeff 1 (A ^ 4) = 0) (p4_2 : coeff 2 (A ^ 4) = 0) (ha2 : coeff 2 A = 0) (p4_3 : coeff 3 (A ^ 4) = 0) (ha3 : coeff 3 A = 2) (p4_4 : coeff 4 (A ^ 4) = 1) (ha4 : coeff 4 A = 0) (p4_5 : coeff 5 (A ^ 4) = 0) (ha5 : coeff 5 A = -6) (p4_6 : coeff 6 (A ^ 4) = 8) (ha6 : coeff 6 A = 0) (p4_7 : coeff 7 (A ^ 4) = 0) (ha7 : coeff 7 A = 36) (p4_8 : coeff 8 (A ^ 4) = 0) : coeff 8 (A ^ 5) = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8]

private theorem cell_p6_8 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p5_0 : coeff 0 (A ^ 5) = 0) (p5_1 : coeff 1 (A ^ 5) = 0) (p5_2 : coeff 2 (A ^ 5) = 0) (ha2 : coeff 2 A = 0) (p5_3 : coeff 3 (A ^ 5) = 0) (ha3 : coeff 3 A = 2) (p5_4 : coeff 4 (A ^ 5) = 0) (ha4 : coeff 4 A = 0) (p5_5 : coeff 5 (A ^ 5) = 1) (ha5 : coeff 5 A = -6) (p5_6 : coeff 6 (A ^ 5) = 0) (ha6 : coeff 6 A = 0) (p5_7 : coeff 7 (A ^ 5) = 10) (ha7 : coeff 7 A = 36) (p5_8 : coeff 8 (A ^ 5) = 0) : coeff 8 (A ^ 6) = 12 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, p5_0, p5_1, p5_2, p5_3, p5_4, p5_5, p5_6, p5_7, p5_8]

private theorem cell_p7_8 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p6_0 : coeff 0 (A ^ 6) = 0) (p6_1 : coeff 1 (A ^ 6) = 0) (p6_2 : coeff 2 (A ^ 6) = 0) (ha2 : coeff 2 A = 0) (p6_3 : coeff 3 (A ^ 6) = 0) (ha3 : coeff 3 A = 2) (p6_4 : coeff 4 (A ^ 6) = 0) (ha4 : coeff 4 A = 0) (p6_5 : coeff 5 (A ^ 6) = 0) (ha5 : coeff 5 A = -6) (p6_6 : coeff 6 (A ^ 6) = 1) (ha6 : coeff 6 A = 0) (p6_7 : coeff 7 (A ^ 6) = 0) (ha7 : coeff 7 A = 36) (p6_8 : coeff 8 (A ^ 6) = 12) : coeff 8 (A ^ 7) = 0 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, p6_0, p6_1, p6_2, p6_3, p6_4, p6_5, p6_6, p6_7, p6_8]

private theorem cell_p8_8 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p7_0 : coeff 0 (A ^ 7) = 0) (p7_1 : coeff 1 (A ^ 7) = 0) (p7_2 : coeff 2 (A ^ 7) = 0) (ha2 : coeff 2 A = 0) (p7_3 : coeff 3 (A ^ 7) = 0) (ha3 : coeff 3 A = 2) (p7_4 : coeff 4 (A ^ 7) = 0) (ha4 : coeff 4 A = 0) (p7_5 : coeff 5 (A ^ 7) = 0) (ha5 : coeff 5 A = -6) (p7_6 : coeff 6 (A ^ 7) = 0) (ha6 : coeff 6 A = 0) (p7_7 : coeff 7 (A ^ 7) = 1) (ha7 : coeff 7 A = 36) (p7_8 : coeff 8 (A ^ 7) = 0) : coeff 8 (A ^ 8) = 1 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, p7_0, p7_1, p7_2, p7_3, p7_4, p7_5, p7_6, p7_7, p7_8]

private theorem cell_p9_8 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p8_0 : coeff 0 (A ^ 8) = 0) (p8_1 : coeff 1 (A ^ 8) = 0) (p8_2 : coeff 2 (A ^ 8) = 0) (ha2 : coeff 2 A = 0) (p8_3 : coeff 3 (A ^ 8) = 0) (ha3 : coeff 3 A = 2) (p8_4 : coeff 4 (A ^ 8) = 0) (ha4 : coeff 4 A = 0) (p8_5 : coeff 5 (A ^ 8) = 0) (ha5 : coeff 5 A = -6) (p8_6 : coeff 6 (A ^ 8) = 0) (ha6 : coeff 6 A = 0) (p8_7 : coeff 7 (A ^ 8) = 0) (ha7 : coeff 7 A = 36) (p8_8 : coeff 8 (A ^ 8) = 1) : coeff 8 (A ^ 9) = 0 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, p8_0, p8_1, p8_2, p8_3, p8_4, p8_5, p8_6, p8_7, p8_8]

private theorem cell_ha8 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0) (hA : A.subst A = X + 4 * X ^ 3) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 0) (ha3 : coeff 3 A = 2) (ha4 : coeff 4 A = 0) (ha5 : coeff 5 A = -6) (ha6 : coeff 6 A = 0) (ha7 : coeff 7 A = 36) (p2_8 : coeff 8 (A ^ 2) = 48) (p3_8 : coeff 8 (A ^ 3) = 0) (p4_8 : coeff 8 (A ^ 4) = 0) (p5_8 : coeff 8 (A ^ 5) = 0) (p6_8 : coeff 8 (A ^ 6) = 12) (p7_8 : coeff 8 (A ^ 7) = 0) (p8_8 : coeff 8 (A ^ 8) = 1) (_p9_8 : coeff 8 (A ^ 9) = 0) : coeff 8 A = 0 := by
  have he := congrArg (coeff 8) hA
  norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, coeff_X, coeff_X_pow, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, p2_8, p3_8, p4_8, p5_8, p6_8, p7_8, p8_8, _p9_8] at he
  omega

private theorem cell_p2_9 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 0) (ha3 : coeff 3 A = 2) (ha4 : coeff 4 A = 0) (ha5 : coeff 5 A = -6) (ha6 : coeff 6 A = 0) (ha7 : coeff 7 A = 36) (ha8 : coeff 8 A = 0) : coeff 9 (A ^ 2) = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]

private theorem cell_p3_9 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p2_0 : coeff 0 (A ^ 2) = 0) (p2_1 : coeff 1 (A ^ 2) = 0) (p2_2 : coeff 2 (A ^ 2) = 1) (ha2 : coeff 2 A = 0) (p2_3 : coeff 3 (A ^ 2) = 0) (ha3 : coeff 3 A = 2) (p2_4 : coeff 4 (A ^ 2) = 4) (ha4 : coeff 4 A = 0) (p2_5 : coeff 5 (A ^ 2) = 0) (ha5 : coeff 5 A = -6) (p2_6 : coeff 6 (A ^ 2) = -8) (ha6 : coeff 6 A = 0) (p2_7 : coeff 7 (A ^ 2) = 0) (ha7 : coeff 7 A = 36) (p2_8 : coeff 8 (A ^ 2) = 48) (ha8 : coeff 8 A = 0) (p2_9 : coeff 9 (A ^ 2) = 0) : coeff 9 (A ^ 3) = 44 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, p2_0, p2_1, p2_2, p2_3, p2_4, p2_5, p2_6, p2_7, p2_8, p2_9]

private theorem cell_p4_9 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p3_0 : coeff 0 (A ^ 3) = 0) (p3_1 : coeff 1 (A ^ 3) = 0) (p3_2 : coeff 2 (A ^ 3) = 0) (ha2 : coeff 2 A = 0) (p3_3 : coeff 3 (A ^ 3) = 1) (ha3 : coeff 3 A = 2) (p3_4 : coeff 4 (A ^ 3) = 0) (ha4 : coeff 4 A = 0) (p3_5 : coeff 5 (A ^ 3) = 6) (ha5 : coeff 5 A = -6) (p3_6 : coeff 6 (A ^ 3) = 0) (ha6 : coeff 6 A = 0) (p3_7 : coeff 7 (A ^ 3) = -6) (ha7 : coeff 7 A = 36) (p3_8 : coeff 8 (A ^ 3) = 0) (ha8 : coeff 8 A = 0) (p3_9 : coeff 9 (A ^ 3) = 44) : coeff 9 (A ^ 4) = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, p3_0, p3_1, p3_2, p3_3, p3_4, p3_5, p3_6, p3_7, p3_8, p3_9]

private theorem cell_p5_9 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p4_0 : coeff 0 (A ^ 4) = 0) (p4_1 : coeff 1 (A ^ 4) = 0) (p4_2 : coeff 2 (A ^ 4) = 0) (ha2 : coeff 2 A = 0) (p4_3 : coeff 3 (A ^ 4) = 0) (ha3 : coeff 3 A = 2) (p4_4 : coeff 4 (A ^ 4) = 1) (ha4 : coeff 4 A = 0) (p4_5 : coeff 5 (A ^ 4) = 0) (ha5 : coeff 5 A = -6) (p4_6 : coeff 6 (A ^ 4) = 8) (ha6 : coeff 6 A = 0) (p4_7 : coeff 7 (A ^ 4) = 0) (ha7 : coeff 7 A = 36) (p4_8 : coeff 8 (A ^ 4) = 0) (ha8 : coeff 8 A = 0) (p4_9 : coeff 9 (A ^ 4) = 0) : coeff 9 (A ^ 5) = 10 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, p4_0, p4_1, p4_2, p4_3, p4_4, p4_5, p4_6, p4_7, p4_8, p4_9]

private theorem cell_p6_9 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p5_0 : coeff 0 (A ^ 5) = 0) (p5_1 : coeff 1 (A ^ 5) = 0) (p5_2 : coeff 2 (A ^ 5) = 0) (ha2 : coeff 2 A = 0) (p5_3 : coeff 3 (A ^ 5) = 0) (ha3 : coeff 3 A = 2) (p5_4 : coeff 4 (A ^ 5) = 0) (ha4 : coeff 4 A = 0) (p5_5 : coeff 5 (A ^ 5) = 1) (ha5 : coeff 5 A = -6) (p5_6 : coeff 6 (A ^ 5) = 0) (ha6 : coeff 6 A = 0) (p5_7 : coeff 7 (A ^ 5) = 10) (ha7 : coeff 7 A = 36) (p5_8 : coeff 8 (A ^ 5) = 0) (ha8 : coeff 8 A = 0) (p5_9 : coeff 9 (A ^ 5) = 10) : coeff 9 (A ^ 6) = 0 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, p5_0, p5_1, p5_2, p5_3, p5_4, p5_5, p5_6, p5_7, p5_8, p5_9]

private theorem cell_p7_9 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p6_0 : coeff 0 (A ^ 6) = 0) (p6_1 : coeff 1 (A ^ 6) = 0) (p6_2 : coeff 2 (A ^ 6) = 0) (ha2 : coeff 2 A = 0) (p6_3 : coeff 3 (A ^ 6) = 0) (ha3 : coeff 3 A = 2) (p6_4 : coeff 4 (A ^ 6) = 0) (ha4 : coeff 4 A = 0) (p6_5 : coeff 5 (A ^ 6) = 0) (ha5 : coeff 5 A = -6) (p6_6 : coeff 6 (A ^ 6) = 1) (ha6 : coeff 6 A = 0) (p6_7 : coeff 7 (A ^ 6) = 0) (ha7 : coeff 7 A = 36) (p6_8 : coeff 8 (A ^ 6) = 12) (ha8 : coeff 8 A = 0) (p6_9 : coeff 9 (A ^ 6) = 0) : coeff 9 (A ^ 7) = 14 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, p6_0, p6_1, p6_2, p6_3, p6_4, p6_5, p6_6, p6_7, p6_8, p6_9]

private theorem cell_p8_9 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p7_0 : coeff 0 (A ^ 7) = 0) (p7_1 : coeff 1 (A ^ 7) = 0) (p7_2 : coeff 2 (A ^ 7) = 0) (ha2 : coeff 2 A = 0) (p7_3 : coeff 3 (A ^ 7) = 0) (ha3 : coeff 3 A = 2) (p7_4 : coeff 4 (A ^ 7) = 0) (ha4 : coeff 4 A = 0) (p7_5 : coeff 5 (A ^ 7) = 0) (ha5 : coeff 5 A = -6) (p7_6 : coeff 6 (A ^ 7) = 0) (ha6 : coeff 6 A = 0) (p7_7 : coeff 7 (A ^ 7) = 1) (ha7 : coeff 7 A = 36) (p7_8 : coeff 8 (A ^ 7) = 0) (ha8 : coeff 8 A = 0) (p7_9 : coeff 9 (A ^ 7) = 14) : coeff 9 (A ^ 8) = 0 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, p7_0, p7_1, p7_2, p7_3, p7_4, p7_5, p7_6, p7_7, p7_8, p7_9]

private theorem cell_p9_9 (A : PowerSeries ℤ) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (p8_0 : coeff 0 (A ^ 8) = 0) (p8_1 : coeff 1 (A ^ 8) = 0) (p8_2 : coeff 2 (A ^ 8) = 0) (ha2 : coeff 2 A = 0) (p8_3 : coeff 3 (A ^ 8) = 0) (ha3 : coeff 3 A = 2) (p8_4 : coeff 4 (A ^ 8) = 0) (ha4 : coeff 4 A = 0) (p8_5 : coeff 5 (A ^ 8) = 0) (ha5 : coeff 5 A = -6) (p8_6 : coeff 6 (A ^ 8) = 0) (ha6 : coeff 6 A = 0) (p8_7 : coeff 7 (A ^ 8) = 0) (ha7 : coeff 7 A = 36) (p8_8 : coeff 8 (A ^ 8) = 1) (ha8 : coeff 8 A = 0) (p8_9 : coeff 9 (A ^ 8) = 0) : coeff 9 (A ^ 9) = 1 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, pow_succ, coeff_mul_range]
  norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, p8_0, p8_1, p8_2, p8_3, p8_4, p8_5, p8_6, p8_7, p8_8, p8_9]

private theorem cell_ha9 (A : PowerSeries ℤ) (h0 : constantCoeff A = 0) (hA : A.subst A = X + 4 * X ^ 3) (ha0 : coeff 0 A = 0) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 0) (ha3 : coeff 3 A = 2) (ha4 : coeff 4 A = 0) (ha5 : coeff 5 A = -6) (ha6 : coeff 6 A = 0) (ha7 : coeff 7 A = 36) (ha8 : coeff 8 A = 0) (p2_9 : coeff 9 (A ^ 2) = 0) (p3_9 : coeff 9 (A ^ 3) = 44) (p4_9 : coeff 9 (A ^ 4) = 0) (p5_9 : coeff 9 (A ^ 5) = 10) (p6_9 : coeff 9 (A ^ 6) = 0) (p7_9 : coeff 9 (A ^ 7) = 14) (p8_9 : coeff 9 (A ^ 8) = 0) (p9_9 : coeff 9 (A ^ 9) = 1) : coeff 9 A = -266 := by
  have he := congrArg (coeff 9) hA
  norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, coeff_X, coeff_X_pow, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, p2_9, p3_9, p4_9, p5_9, p6_9, p7_9, p8_9, p9_9] at he
  omega

theorem check_DATA_A107099 : DATA_A107099 := by
  intro A h0 h1 hA
  change A.subst A = X + 4 * X ^ 3 at hA
  have ha0 : coeff 0 A = 0 := cell_ha0 A h0
  have ha1 : coeff 1 A = 1 := cell_ha1 A h1
  have p2_0 : coeff 0 (A ^ 2) = 0 := cell_p2_0 A ha0
  have p3_0 : coeff 0 (A ^ 3) = 0 := cell_p3_0 A ha0 p2_0
  have p4_0 : coeff 0 (A ^ 4) = 0 := cell_p4_0 A ha0 p3_0
  have p5_0 : coeff 0 (A ^ 5) = 0 := cell_p5_0 A ha0 p4_0
  have p6_0 : coeff 0 (A ^ 6) = 0 := cell_p6_0 A ha0 p5_0
  have p7_0 : coeff 0 (A ^ 7) = 0 := cell_p7_0 A ha0 p6_0
  have p8_0 : coeff 0 (A ^ 8) = 0 := cell_p8_0 A ha0 p7_0
  have p9_0 : coeff 0 (A ^ 9) = 0 := cell_p9_0 A ha0 p8_0
  have p2_1 : coeff 1 (A ^ 2) = 0 := cell_p2_1 A ha0 ha1
  have p3_1 : coeff 1 (A ^ 3) = 0 := cell_p3_1 A ha0 ha1 p2_0 p2_1
  have p4_1 : coeff 1 (A ^ 4) = 0 := cell_p4_1 A ha0 ha1 p3_0 p3_1
  have p5_1 : coeff 1 (A ^ 5) = 0 := cell_p5_1 A ha0 ha1 p4_0 p4_1
  have p6_1 : coeff 1 (A ^ 6) = 0 := cell_p6_1 A ha0 ha1 p5_0 p5_1
  have p7_1 : coeff 1 (A ^ 7) = 0 := cell_p7_1 A ha0 ha1 p6_0 p6_1
  have p8_1 : coeff 1 (A ^ 8) = 0 := cell_p8_1 A ha0 ha1 p7_0 p7_1
  have p9_1 : coeff 1 (A ^ 9) = 0 := cell_p9_1 A ha0 ha1 p8_0 p8_1
  have p2_2 : coeff 2 (A ^ 2) = 1 := cell_p2_2 A ha0 ha1
  have p3_2 : coeff 2 (A ^ 3) = 0 := cell_p3_2 A ha0 ha1 p2_0 p2_1 p2_2
  have p4_2 : coeff 2 (A ^ 4) = 0 := cell_p4_2 A ha0 ha1 p3_0 p3_1 p3_2
  have p5_2 : coeff 2 (A ^ 5) = 0 := cell_p5_2 A ha0 ha1 p4_0 p4_1 p4_2
  have p6_2 : coeff 2 (A ^ 6) = 0 := cell_p6_2 A ha0 ha1 p5_0 p5_1 p5_2
  have p7_2 : coeff 2 (A ^ 7) = 0 := cell_p7_2 A ha0 ha1 p6_0 p6_1 p6_2
  have p8_2 : coeff 2 (A ^ 8) = 0 := cell_p8_2 A ha0 ha1 p7_0 p7_1 p7_2
  have p9_2 : coeff 2 (A ^ 9) = 0 := cell_p9_2 A ha0 ha1 p8_0 p8_1 p8_2
  have ha2 : coeff 2 A = 0 := cell_ha2 A h0 hA ha0 ha1 p2_2 p3_2 p4_2 p5_2 p6_2 p7_2 p8_2 p9_2
  have p2_3 : coeff 3 (A ^ 2) = 0 := cell_p2_3 A ha0 ha1 ha2
  have p3_3 : coeff 3 (A ^ 3) = 1 := cell_p3_3 A ha0 ha1 p2_0 p2_1 p2_2 ha2 p2_3
  have p4_3 : coeff 3 (A ^ 4) = 0 := cell_p4_3 A ha0 ha1 p3_0 p3_1 p3_2 ha2 p3_3
  have p5_3 : coeff 3 (A ^ 5) = 0 := cell_p5_3 A ha0 ha1 p4_0 p4_1 p4_2 ha2 p4_3
  have p6_3 : coeff 3 (A ^ 6) = 0 := cell_p6_3 A ha0 ha1 p5_0 p5_1 p5_2 ha2 p5_3
  have p7_3 : coeff 3 (A ^ 7) = 0 := cell_p7_3 A ha0 ha1 p6_0 p6_1 p6_2 ha2 p6_3
  have p8_3 : coeff 3 (A ^ 8) = 0 := cell_p8_3 A ha0 ha1 p7_0 p7_1 p7_2 ha2 p7_3
  have p9_3 : coeff 3 (A ^ 9) = 0 := cell_p9_3 A ha0 ha1 p8_0 p8_1 p8_2 ha2 p8_3
  have ha3 : coeff 3 A = 2 := cell_ha3 A h0 hA ha0 ha1 ha2 p2_3 p3_3 p4_3 p5_3 p6_3 p7_3 p8_3 p9_3
  have p2_4 : coeff 4 (A ^ 2) = 4 := cell_p2_4 A ha0 ha1 ha2 ha3
  have p3_4 : coeff 4 (A ^ 3) = 0 := cell_p3_4 A ha0 ha1 p2_0 p2_1 p2_2 ha2 p2_3 ha3 p2_4
  have p4_4 : coeff 4 (A ^ 4) = 1 := cell_p4_4 A ha0 ha1 p3_0 p3_1 p3_2 ha2 p3_3 ha3 p3_4
  have p5_4 : coeff 4 (A ^ 5) = 0 := cell_p5_4 A ha0 ha1 p4_0 p4_1 p4_2 ha2 p4_3 ha3 p4_4
  have p6_4 : coeff 4 (A ^ 6) = 0 := cell_p6_4 A ha0 ha1 p5_0 p5_1 p5_2 ha2 p5_3 ha3 p5_4
  have p7_4 : coeff 4 (A ^ 7) = 0 := cell_p7_4 A ha0 ha1 p6_0 p6_1 p6_2 ha2 p6_3 ha3 p6_4
  have p8_4 : coeff 4 (A ^ 8) = 0 := cell_p8_4 A ha0 ha1 p7_0 p7_1 p7_2 ha2 p7_3 ha3 p7_4
  have p9_4 : coeff 4 (A ^ 9) = 0 := cell_p9_4 A ha0 ha1 p8_0 p8_1 p8_2 ha2 p8_3 ha3 p8_4
  have ha4 : coeff 4 A = 0 := cell_ha4 A h0 hA ha0 ha1 ha2 ha3 p2_4 p3_4 p4_4 p5_4 p6_4 p7_4 p8_4 p9_4
  have p2_5 : coeff 5 (A ^ 2) = 0 := cell_p2_5 A ha0 ha1 ha2 ha3 ha4
  have p3_5 : coeff 5 (A ^ 3) = 6 := cell_p3_5 A ha0 ha1 p2_0 p2_1 p2_2 ha2 p2_3 ha3 p2_4 ha4 p2_5
  have p4_5 : coeff 5 (A ^ 4) = 0 := cell_p4_5 A ha0 ha1 p3_0 p3_1 p3_2 ha2 p3_3 ha3 p3_4 ha4 p3_5
  have p5_5 : coeff 5 (A ^ 5) = 1 := cell_p5_5 A ha0 ha1 p4_0 p4_1 p4_2 ha2 p4_3 ha3 p4_4 ha4 p4_5
  have p6_5 : coeff 5 (A ^ 6) = 0 := cell_p6_5 A ha0 ha1 p5_0 p5_1 p5_2 ha2 p5_3 ha3 p5_4 ha4 p5_5
  have p7_5 : coeff 5 (A ^ 7) = 0 := cell_p7_5 A ha0 ha1 p6_0 p6_1 p6_2 ha2 p6_3 ha3 p6_4 ha4 p6_5
  have p8_5 : coeff 5 (A ^ 8) = 0 := cell_p8_5 A ha0 ha1 p7_0 p7_1 p7_2 ha2 p7_3 ha3 p7_4 ha4 p7_5
  have p9_5 : coeff 5 (A ^ 9) = 0 := cell_p9_5 A ha0 ha1 p8_0 p8_1 p8_2 ha2 p8_3 ha3 p8_4 ha4 p8_5
  have ha5 : coeff 5 A = -6 := cell_ha5 A h0 hA ha0 ha1 ha2 ha3 ha4 p2_5 p3_5 p4_5 p5_5 p6_5 p7_5 p8_5 p9_5
  have p2_6 : coeff 6 (A ^ 2) = -8 := cell_p2_6 A ha0 ha1 ha2 ha3 ha4 ha5
  have p3_6 : coeff 6 (A ^ 3) = 0 := cell_p3_6 A ha0 ha1 p2_0 p2_1 p2_2 ha2 p2_3 ha3 p2_4 ha4 p2_5 ha5 p2_6
  have p4_6 : coeff 6 (A ^ 4) = 8 := cell_p4_6 A ha0 ha1 p3_0 p3_1 p3_2 ha2 p3_3 ha3 p3_4 ha4 p3_5 ha5 p3_6
  have p5_6 : coeff 6 (A ^ 5) = 0 := cell_p5_6 A ha0 ha1 p4_0 p4_1 p4_2 ha2 p4_3 ha3 p4_4 ha4 p4_5 ha5 p4_6
  have p6_6 : coeff 6 (A ^ 6) = 1 := cell_p6_6 A ha0 ha1 p5_0 p5_1 p5_2 ha2 p5_3 ha3 p5_4 ha4 p5_5 ha5 p5_6
  have p7_6 : coeff 6 (A ^ 7) = 0 := cell_p7_6 A ha0 ha1 p6_0 p6_1 p6_2 ha2 p6_3 ha3 p6_4 ha4 p6_5 ha5 p6_6
  have p8_6 : coeff 6 (A ^ 8) = 0 := cell_p8_6 A ha0 ha1 p7_0 p7_1 p7_2 ha2 p7_3 ha3 p7_4 ha4 p7_5 ha5 p7_6
  have p9_6 : coeff 6 (A ^ 9) = 0 := cell_p9_6 A ha0 ha1 p8_0 p8_1 p8_2 ha2 p8_3 ha3 p8_4 ha4 p8_5 ha5 p8_6
  have ha6 : coeff 6 A = 0 := cell_ha6 A h0 hA ha0 ha1 ha2 ha3 ha4 ha5 p2_6 p3_6 p4_6 p5_6 p6_6 p7_6 p8_6 p9_6
  have p2_7 : coeff 7 (A ^ 2) = 0 := cell_p2_7 A ha0 ha1 ha2 ha3 ha4 ha5 ha6
  have p3_7 : coeff 7 (A ^ 3) = -6 := cell_p3_7 A ha0 ha1 p2_0 p2_1 p2_2 ha2 p2_3 ha3 p2_4 ha4 p2_5 ha5 p2_6 ha6 p2_7
  have p4_7 : coeff 7 (A ^ 4) = 0 := cell_p4_7 A ha0 ha1 p3_0 p3_1 p3_2 ha2 p3_3 ha3 p3_4 ha4 p3_5 ha5 p3_6 ha6 p3_7
  have p5_7 : coeff 7 (A ^ 5) = 10 := cell_p5_7 A ha0 ha1 p4_0 p4_1 p4_2 ha2 p4_3 ha3 p4_4 ha4 p4_5 ha5 p4_6 ha6 p4_7
  have p6_7 : coeff 7 (A ^ 6) = 0 := cell_p6_7 A ha0 ha1 p5_0 p5_1 p5_2 ha2 p5_3 ha3 p5_4 ha4 p5_5 ha5 p5_6 ha6 p5_7
  have p7_7 : coeff 7 (A ^ 7) = 1 := cell_p7_7 A ha0 ha1 p6_0 p6_1 p6_2 ha2 p6_3 ha3 p6_4 ha4 p6_5 ha5 p6_6 ha6 p6_7
  have p8_7 : coeff 7 (A ^ 8) = 0 := cell_p8_7 A ha0 ha1 p7_0 p7_1 p7_2 ha2 p7_3 ha3 p7_4 ha4 p7_5 ha5 p7_6 ha6 p7_7
  have p9_7 : coeff 7 (A ^ 9) = 0 := cell_p9_7 A ha0 ha1 p8_0 p8_1 p8_2 ha2 p8_3 ha3 p8_4 ha4 p8_5 ha5 p8_6 ha6 p8_7
  have ha7 : coeff 7 A = 36 := cell_ha7 A h0 hA ha0 ha1 ha2 ha3 ha4 ha5 ha6 p2_7 p3_7 p4_7 p5_7 p6_7 p7_7 p8_7 p9_7
  have p2_8 : coeff 8 (A ^ 2) = 48 := cell_p2_8 A ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
  have p3_8 : coeff 8 (A ^ 3) = 0 := cell_p3_8 A ha0 ha1 p2_0 p2_1 p2_2 ha2 p2_3 ha3 p2_4 ha4 p2_5 ha5 p2_6 ha6 p2_7 ha7 p2_8
  have p4_8 : coeff 8 (A ^ 4) = 0 := cell_p4_8 A ha0 ha1 p3_0 p3_1 p3_2 ha2 p3_3 ha3 p3_4 ha4 p3_5 ha5 p3_6 ha6 p3_7 ha7 p3_8
  have p5_8 : coeff 8 (A ^ 5) = 0 := cell_p5_8 A ha0 ha1 p4_0 p4_1 p4_2 ha2 p4_3 ha3 p4_4 ha4 p4_5 ha5 p4_6 ha6 p4_7 ha7 p4_8
  have p6_8 : coeff 8 (A ^ 6) = 12 := cell_p6_8 A ha0 ha1 p5_0 p5_1 p5_2 ha2 p5_3 ha3 p5_4 ha4 p5_5 ha5 p5_6 ha6 p5_7 ha7 p5_8
  have p7_8 : coeff 8 (A ^ 7) = 0 := cell_p7_8 A ha0 ha1 p6_0 p6_1 p6_2 ha2 p6_3 ha3 p6_4 ha4 p6_5 ha5 p6_6 ha6 p6_7 ha7 p6_8
  have p8_8 : coeff 8 (A ^ 8) = 1 := cell_p8_8 A ha0 ha1 p7_0 p7_1 p7_2 ha2 p7_3 ha3 p7_4 ha4 p7_5 ha5 p7_6 ha6 p7_7 ha7 p7_8
  have p9_8 : coeff 8 (A ^ 9) = 0 := cell_p9_8 A ha0 ha1 p8_0 p8_1 p8_2 ha2 p8_3 ha3 p8_4 ha4 p8_5 ha5 p8_6 ha6 p8_7 ha7 p8_8
  have ha8 : coeff 8 A = 0 := cell_ha8 A h0 hA ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 p2_8 p3_8 p4_8 p5_8 p6_8 p7_8 p8_8 p9_8
  have p2_9 : coeff 9 (A ^ 2) = 0 := cell_p2_9 A ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8
  have p3_9 : coeff 9 (A ^ 3) = 44 := cell_p3_9 A ha0 ha1 p2_0 p2_1 p2_2 ha2 p2_3 ha3 p2_4 ha4 p2_5 ha5 p2_6 ha6 p2_7 ha7 p2_8 ha8 p2_9
  have p4_9 : coeff 9 (A ^ 4) = 0 := cell_p4_9 A ha0 ha1 p3_0 p3_1 p3_2 ha2 p3_3 ha3 p3_4 ha4 p3_5 ha5 p3_6 ha6 p3_7 ha7 p3_8 ha8 p3_9
  have p5_9 : coeff 9 (A ^ 5) = 10 := cell_p5_9 A ha0 ha1 p4_0 p4_1 p4_2 ha2 p4_3 ha3 p4_4 ha4 p4_5 ha5 p4_6 ha6 p4_7 ha7 p4_8 ha8 p4_9
  have p6_9 : coeff 9 (A ^ 6) = 0 := cell_p6_9 A ha0 ha1 p5_0 p5_1 p5_2 ha2 p5_3 ha3 p5_4 ha4 p5_5 ha5 p5_6 ha6 p5_7 ha7 p5_8 ha8 p5_9
  have p7_9 : coeff 9 (A ^ 7) = 14 := cell_p7_9 A ha0 ha1 p6_0 p6_1 p6_2 ha2 p6_3 ha3 p6_4 ha4 p6_5 ha5 p6_6 ha6 p6_7 ha7 p6_8 ha8 p6_9
  have p8_9 : coeff 9 (A ^ 8) = 0 := cell_p8_9 A ha0 ha1 p7_0 p7_1 p7_2 ha2 p7_3 ha3 p7_4 ha4 p7_5 ha5 p7_6 ha6 p7_7 ha7 p7_8 ha8 p7_9
  have p9_9 : coeff 9 (A ^ 9) = 1 := cell_p9_9 A ha0 ha1 p8_0 p8_1 p8_2 ha2 p8_3 ha3 p8_4 ha4 p8_5 ha5 p8_6 ha6 p8_7 ha7 p8_8 ha8 p8_9
  have ha9 : coeff 9 A = -266 := cell_ha9 A h0 hA ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 p2_9 p3_9 p4_9 p5_9 p6_9 p7_9 p8_9 p9_9
  exact ⟨ha2, ha3, ha5, ha7, ha9⟩

end BackfillPaper2.DataSelf107099
#print axioms BackfillPaper2.DataSelf107099.check_DATA_A107099
