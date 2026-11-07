import Research.Backfill.Paper2.FiniteCoefficients

/-! Finite exact convolution certificates for every original normalized solution. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.DataTriple120566
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.FiniteCoefficients

theorem check_DATA_A120566 : DATA_A120566 := by
  intro A h0 h1 hA
  let B : PowerSeries ℤ := A.subst A
  have hb0 : constantCoeff B = 0 := constantCoeff_subst_eq_zero h0 A h0
  change A = B - X * A.subst B at hA
  have ha0 : coeff 0 A = 0 := by simpa only [coeff_zero_eq_constantCoeff_apply] using h0
  have ha1 : coeff 1 A = 1 := h1
  have p2_0 : coeff 0 (A ^ 2) = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0]
  have p3_0 : coeff 0 (A ^ 3) = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, p2_0]
  have p4_0 : coeff 0 (A ^ 4) = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, p2_0, p3_0]
  have p5_0 : coeff 0 (A ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, p2_0, p3_0, p4_0]
  have p6_0 : coeff 0 (A ^ 6) = 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, p2_0, p3_0, p4_0, p5_0]
  have b0 : coeff 0 B = 0 := by
    dsimp only [B]
    norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, ha0, ha1]
  have q2_0 : coeff 0 (B ^ 2) = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0]
  have q3_0 : coeff 0 (B ^ 3) = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, q2_0]
  have q4_0 : coeff 0 (B ^ 4) = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, q2_0, q3_0]
  have q5_0 : coeff 0 (B ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, q2_0, q3_0, q4_0]
  have q6_0 : coeff 0 (B ^ 6) = 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, q2_0, q3_0, q4_0, q5_0]
  have p2_1 : coeff 1 (A ^ 2) = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0, p3_0, p4_0, p5_0, p6_0]
  have p3_1 : coeff 1 (A ^ 3) = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1]
  have p4_1 : coeff 1 (A ^ 4) = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1]
  have p5_1 : coeff 1 (A ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1]
  have p6_1 : coeff 1 (A ^ 6) = 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1]
  have b1 : coeff 1 B = 1 := by
    dsimp only [B]
    norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, ha0, ha1]
  have q2_1 : coeff 1 (B ^ 2) = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, q2_0, q3_0, q4_0, q5_0, q6_0]
  have q3_1 : coeff 1 (B ^ 3) = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1]
  have q4_1 : coeff 1 (B ^ 4) = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1]
  have q5_1 : coeff 1 (B ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1]
  have q6_1 : coeff 1 (B ^ 6) = 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1]
  have p2_2 : coeff 2 (A ^ 2) = 1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1]
  have p3_2 : coeff 2 (A ^ 3) = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2]
  have p4_2 : coeff 2 (A ^ 4) = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2]
  have p5_2 : coeff 2 (A ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2]
  have p6_2 : coeff 2 (A ^ 6) = 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2]
  have be2 : coeff 2 B = 2 * coeff 2 A + (0) := by
    dsimp only [B]
    norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, ha0, ha1, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2]
    ring
  have ha2 : coeff 2 A = 1 := by
    have he := congrArg (coeff 2) hA
    norm_num [coeff_subst_range _ _ hb0, Finset.sum_range_succ, coeff_mul_range, coeff_X, ha0, ha1, b0, b1, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, be2] at he
    omega
  have b2 : coeff 2 B = 2 := by rw [be2, ha2]; norm_num
  have q2_2 : coeff 2 (B ^ 2) = 1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1]
  have q3_2 : coeff 2 (B ^ 3) = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2]
  have q4_2 : coeff 2 (B ^ 4) = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2]
  have q5_2 : coeff 2 (B ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2]
  have q6_2 : coeff 2 (B ^ 6) = 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2]
  have p2_3 : coeff 3 (A ^ 2) = 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2]
  have p3_3 : coeff 3 (A ^ 3) = 1 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3]
  have p4_3 : coeff 3 (A ^ 4) = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3]
  have p5_3 : coeff 3 (A ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3]
  have p6_3 : coeff 3 (A ^ 6) = 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3]
  have be3 : coeff 3 B = 2 * coeff 3 A + (2) := by
    dsimp only [B]
    norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, ha0, ha1, ha2, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3]
    ring
  have ha3 : coeff 3 A = 1 := by
    have he := congrArg (coeff 3) hA
    norm_num [coeff_subst_range _ _ hb0, Finset.sum_range_succ, coeff_mul_range, coeff_X, ha0, ha1, ha2, b0, b1, b2, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, be3] at he
    omega
  have b3 : coeff 3 B = 4 := by rw [be3, ha3]; norm_num
  have q2_3 : coeff 3 (B ^ 2) = 4 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2]
  have q3_3 : coeff 3 (B ^ 3) = 1 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3]
  have q4_3 : coeff 3 (B ^ 4) = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3]
  have q5_3 : coeff 3 (B ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3]
  have q6_3 : coeff 3 (B ^ 6) = 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3]
  have p2_4 : coeff 4 (A ^ 2) = 3 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3]
  have p3_4 : coeff 4 (A ^ 3) = 3 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4]
  have p4_4 : coeff 4 (A ^ 4) = 1 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4]
  have p5_4 : coeff 4 (A ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4]
  have p6_4 : coeff 4 (A ^ 6) = 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4, p5_4]
  have be4 : coeff 4 B = 2 * coeff 4 A + (6) := by
    dsimp only [B]
    norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, ha0, ha1, ha2, ha3, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4, p5_4, p6_4]
    ring
  have ha4 : coeff 4 A = 3 := by
    have he := congrArg (coeff 4) hA
    norm_num [coeff_subst_range _ _ hb0, Finset.sum_range_succ, coeff_mul_range, coeff_X, ha0, ha1, ha2, ha3, b0, b1, b2, b3, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, be4] at he
    omega
  have b4 : coeff 4 B = 12 := by rw [be4, ha4]; norm_num
  have q2_4 : coeff 4 (B ^ 2) = 12 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3]
  have q3_4 : coeff 4 (B ^ 3) = 6 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4]
  have q4_4 : coeff 4 (B ^ 4) = 1 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4]
  have q5_4 : coeff 4 (B ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4, q4_4]
  have q6_4 : coeff 4 (B ^ 6) = 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4, q4_4, q5_4]
  have p2_5 : coeff 5 (A ^ 2) = 8 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4, p5_4, p6_4]
  have p3_5 : coeff 5 (A ^ 3) = 6 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4, p5_4, p6_4, p2_5]
  have p4_5 : coeff 5 (A ^ 4) = 4 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4, p5_4, p6_4, p2_5, p3_5]
  have p5_5 : coeff 5 (A ^ 5) = 1 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4, p5_4, p6_4, p2_5, p3_5, p4_5]
  have p6_5 : coeff 5 (A ^ 6) = 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4, p5_4, p6_4, p2_5, p3_5, p4_5, p5_5]
  have be5 : coeff 5 B = 2 * coeff 5 A + (26) := by
    dsimp only [B]
    norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4, p5_4, p6_4, p2_5, p3_5, p4_5, p5_5, p6_5]
    ring
  have ha5 : coeff 5 A = 7 := by
    have he := congrArg (coeff 5) hA
    norm_num [coeff_subst_range _ _ hb0, Finset.sum_range_succ, coeff_mul_range, coeff_X, ha0, ha1, ha2, ha3, ha4, b0, b1, b2, b3, b4, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4, q4_4, q5_4, q6_4, be5] at he
    omega
  have b5 : coeff 5 B = 40 := by rw [be5, ha5]; norm_num
  have q2_5 : coeff 5 (B ^ 2) = 40 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, b5, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4, q4_4, q5_4, q6_4]
  have q3_5 : coeff 5 (B ^ 3) = 24 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, b5, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4, q4_4, q5_4, q6_4, q2_5]
  have q4_5 : coeff 5 (B ^ 4) = 8 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, b5, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4, q4_4, q5_4, q6_4, q2_5, q3_5]
  have q5_5 : coeff 5 (B ^ 5) = 1 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, b5, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4, q4_4, q5_4, q6_4, q2_5, q3_5, q4_5]
  have q6_5 : coeff 5 (B ^ 6) = 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, b5, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4, q4_4, q5_4, q6_4, q2_5, q3_5, q4_5, q5_5]
  have p2_6 : coeff 6 (A ^ 2) = 21 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4, p5_4, p6_4, p2_5, p3_5, p4_5, p5_5, p6_5]
  have p3_6 : coeff 6 (A ^ 3) = 16 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4, p5_4, p6_4, p2_5, p3_5, p4_5, p5_5, p6_5, p2_6]
  have p4_6 : coeff 6 (A ^ 4) = 10 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4, p5_4, p6_4, p2_5, p3_5, p4_5, p5_5, p6_5, p2_6, p3_6]
  have p5_6 : coeff 6 (A ^ 5) = 5 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4, p5_4, p6_4, p2_5, p3_5, p4_5, p5_5, p6_5, p2_6, p3_6, p4_6]
  have p6_6 : coeff 6 (A ^ 6) = 1 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, ha5, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4, p5_4, p6_4, p2_5, p3_5, p4_5, p5_5, p6_5, p2_6, p3_6, p4_6, p5_6]
  have be6 : coeff 6 B = 2 * coeff 6 A + (102) := by
    dsimp only [B]
    norm_num [coeff_subst_range _ _ h0, Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4, ha5, p2_0, p3_0, p4_0, p5_0, p6_0, p2_1, p3_1, p4_1, p5_1, p6_1, p2_2, p3_2, p4_2, p5_2, p6_2, p2_3, p3_3, p4_3, p5_3, p6_3, p2_4, p3_4, p4_4, p5_4, p6_4, p2_5, p3_5, p4_5, p5_5, p6_5, p2_6, p3_6, p4_6, p5_6, p6_6]
    ring
  have ha6 : coeff 6 A = 33 := by
    have he := congrArg (coeff 6) hA
    norm_num [coeff_subst_range _ _ hb0, Finset.sum_range_succ, coeff_mul_range, coeff_X, ha0, ha1, ha2, ha3, ha4, ha5, b0, b1, b2, b3, b4, b5, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4, q4_4, q5_4, q6_4, q2_5, q3_5, q4_5, q5_5, q6_5, be6] at he
    omega
  have b6 : coeff 6 B = 168 := by rw [be6, ha6]; norm_num
  have q2_6 : coeff 6 (B ^ 2) = 144 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, b5, b6, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4, q4_4, q5_4, q6_4, q2_5, q3_5, q4_5, q5_5, q6_5]
  have q3_6 : coeff 6 (B ^ 3) = 92 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, b5, b6, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4, q4_4, q5_4, q6_4, q2_5, q3_5, q4_5, q5_5, q6_5, q2_6]
  have q4_6 : coeff 6 (B ^ 4) = 40 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, b5, b6, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4, q4_4, q5_4, q6_4, q2_5, q3_5, q4_5, q5_5, q6_5, q2_6, q3_6]
  have q5_6 : coeff 6 (B ^ 5) = 10 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, b5, b6, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4, q4_4, q5_4, q6_4, q2_5, q3_5, q4_5, q5_5, q6_5, q2_6, q3_6, q4_6]
  have q6_6 : coeff 6 (B ^ 6) = 1 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, b0, b1, b2, b3, b4, b5, b6, q2_0, q3_0, q4_0, q5_0, q6_0, q2_1, q3_1, q4_1, q5_1, q6_1, q2_2, q3_2, q4_2, q5_2, q6_2, q2_3, q3_3, q4_3, q5_3, q6_3, q2_4, q3_4, q4_4, q5_4, q6_4, q2_5, q3_5, q4_5, q5_5, q6_5, q2_6, q3_6, q4_6, q5_6]
  exact ⟨ha2, ha3, ha4, ha5, ha6⟩

end BackfillPaper2.DataTriple120566
#print axioms BackfillPaper2.DataTriple120566.check_DATA_A120566
