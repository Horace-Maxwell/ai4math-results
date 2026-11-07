import Research.Backfill.Paper2.FiniteCoefficients

/-! Every finite table cell is proved from exact convolution. No table is a premise. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.DataSubstitution295762
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.FiniteCoefficients

theorem check_DATA_A295762 : DATA_A295762 := by
  intro A h0 hA
  let h : PowerSeries ℤ := X - 2 * A.subst (X ^ 2)
  change A.subst h = X + A.subst (X ^ 2) at hA
  have ha0 : coeff 0 A = 0 := by simpa only [coeff_zero_eq_constantCoeff_apply] using h0
  have hh0 : constantCoeff h = 0 := by simp [h, constantCoeff_subst_X_pow two_ne_zero, h0]
  have h0 : coeff 0 h = 0 := by
    simpa only [coeff_zero_eq_constantCoeff_apply] using hh0
  have p2_0 : coeff 0 (h ^ 2) = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0]
  have p3_0 : coeff 0 (h ^ 3) = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, p2_0]
  have p4_0 : coeff 0 (h ^ 4) = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, p2_0, p3_0]
  have p5_0 : coeff 0 (h ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, p2_0, p3_0, p4_0]
  have h1 : coeff 1 h = 1 := by
    norm_num [h, coeff_mul_range, coeff_subst_X_pow two_ne_zero, coeff_X_pow_mul', coeff_X, coeff_derivative, Finset.sum_range_succ, ha0]
  have p2_1 : coeff 1 (h ^ 2) = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, p2_0, p3_0, p4_0, p5_0]
  have p3_1 : coeff 1 (h ^ 3) = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, p2_0, p3_0, p4_0, p5_0, p2_1]
  have p4_1 : coeff 1 (h ^ 4) = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1]
  have p5_1 : coeff 1 (h ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1]
  have ha1 : coeff 1 A = 1 := by
    have he := congrArg (coeff 1) hA
    norm_num [coeff_subst_range _ _ hh0, coeff_subst_X_pow two_ne_zero, Finset.sum_range_succ, coeff_X, pow_one, ha0, h0, h1, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1] at he
    omega
  have h2 : coeff 2 h = -2 := by
    norm_num [h, coeff_mul_range, coeff_subst_X_pow two_ne_zero, coeff_X_pow_mul', coeff_X, coeff_derivative, Finset.sum_range_succ, ha0, ha1]
  have p2_2 : coeff 2 (h ^ 2) = 1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1]
  have p3_2 : coeff 2 (h ^ 3) = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2]
  have p4_2 : coeff 2 (h ^ 4) = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2]
  have p5_2 : coeff 2 (h ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2]
  have ha2 : coeff 2 A = 3 := by
    have he := congrArg (coeff 2) hA
    norm_num [coeff_subst_range _ _ hh0, coeff_subst_X_pow two_ne_zero, Finset.sum_range_succ, coeff_X, pow_one, ha0, ha1, h0, h1, h2, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2] at he
    omega
  have h3 : coeff 3 h = 0 := by
    norm_num [h, coeff_mul_range, coeff_subst_X_pow two_ne_zero, coeff_X_pow_mul', coeff_X, coeff_derivative, Finset.sum_range_succ, ha0, ha1, ha2]
  have p2_3 : coeff 3 (h ^ 2) = -4 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2]
  have p3_3 : coeff 3 (h ^ 3) = 1 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2, p2_3]
  have p4_3 : coeff 3 (h ^ 4) = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2, p2_3, p3_3]
  have p5_3 : coeff 3 (h ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2, p2_3, p3_3, p4_3]
  have ha3 : coeff 3 A = 12 := by
    have he := congrArg (coeff 3) hA
    norm_num [coeff_subst_range _ _ hh0, coeff_subst_X_pow two_ne_zero, Finset.sum_range_succ, coeff_X, pow_one, ha0, ha1, ha2, h0, h1, h2, h3, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2, p2_3, p3_3, p4_3, p5_3] at he
    omega
  have h4 : coeff 4 h = -6 := by
    norm_num [h, coeff_mul_range, coeff_subst_X_pow two_ne_zero, coeff_X_pow_mul', coeff_X, coeff_derivative, Finset.sum_range_succ, ha0, ha1, ha2, ha3]
  have p2_4 : coeff 4 (h ^ 2) = 4 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2, p2_3, p3_3, p4_3, p5_3]
  have p3_4 : coeff 4 (h ^ 3) = -6 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2, p2_3, p3_3, p4_3, p5_3, p2_4]
  have p4_4 : coeff 4 (h ^ 4) = 1 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2, p2_3, p3_3, p4_3, p5_3, p2_4, p3_4]
  have p5_4 : coeff 4 (h ^ 5) = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2, p2_3, p3_3, p4_3, p5_3, p2_4, p3_4, p4_4]
  have ha4 : coeff 4 A = 69 := by
    have he := congrArg (coeff 4) hA
    norm_num [coeff_subst_range _ _ hh0, coeff_subst_X_pow two_ne_zero, Finset.sum_range_succ, coeff_X, pow_one, ha0, ha1, ha2, ha3, h0, h1, h2, h3, h4, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2, p2_3, p3_3, p4_3, p5_3, p2_4, p3_4, p4_4, p5_4] at he
    omega
  have h5 : coeff 5 h = 0 := by
    norm_num [h, coeff_mul_range, coeff_subst_X_pow two_ne_zero, coeff_X_pow_mul', coeff_X, coeff_derivative, Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4]
  have p2_5 : coeff 5 (h ^ 2) = -12 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2, p2_3, p3_3, p4_3, p5_3, p2_4, p3_4, p4_4, p5_4]
  have p3_5 : coeff 5 (h ^ 3) = 12 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2, p2_3, p3_3, p4_3, p5_3, p2_4, p3_4, p4_4, p5_4, p2_5]
  have p4_5 : coeff 5 (h ^ 4) = -8 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2, p2_3, p3_3, p4_3, p5_3, p2_4, p3_4, p4_4, p5_4, p2_5, p3_5]
  have p5_5 : coeff 5 (h ^ 5) = 1 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, h0, h1, h2, h3, h4, h5, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2, p2_3, p3_3, p4_3, p5_3, p2_4, p3_4, p4_4, p5_4, p2_5, p3_5, p4_5]
  have ha5 : coeff 5 A = 444 := by
    have he := congrArg (coeff 5) hA
    norm_num [coeff_subst_range _ _ hh0, coeff_subst_X_pow two_ne_zero, Finset.sum_range_succ, coeff_X, pow_one, ha0, ha1, ha2, ha3, ha4, h0, h1, h2, h3, h4, h5, p2_0, p3_0, p4_0, p5_0, p2_1, p3_1, p4_1, p5_1, p2_2, p3_2, p4_2, p5_2, p2_3, p3_3, p4_3, p5_3, p2_4, p3_4, p4_4, p5_4, p2_5, p3_5, p4_5, p5_5] at he
    omega
  exact ⟨ha1, ha2, ha3, ha4, ha5⟩

end BackfillPaper2.DataSubstitution295762
#print axioms BackfillPaper2.DataSubstitution295762.check_DATA_A295762
