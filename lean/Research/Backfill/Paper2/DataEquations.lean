import Research.Backfill.Paper2.FiniteCoefficients

/-! Original DATA gates, by exact coefficient identities for every original solution. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.DataEquations
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.FiniteCoefficients

theorem check_DATA_A389472 : DATA_A389472 := by
  intro A ha2 hA
  let h : PowerSeries ℤ := X ^ 2 + X ^ 3
  have h0 : constantCoeff h = 0 := by simp [h]
  have ha0 : coeff 0 A = 0 := by
    have he := congrArg (coeff 0) hA
    norm_num [h, coeff_subst_range _ _ h0, coeff_h389472_pow, Nat.choose, Finset.sum_range_succ] at he
    simpa only [coeff_zero_eq_constantCoeff_apply] using he
  have ha1 : coeff 1 A = 1 := by
    have he := congrArg (coeff 2) hA
    norm_num [h, coeff_subst_range _ _ h0, coeff_h389472_pow, Nat.choose, Finset.sum_range_succ,
      coeff_X_pow_mul', ha0] at he
    simpa only [← coeff_zero_eq_constantCoeff_apply, ha0, add_zero] using he
  have ha3 : coeff 3 A = 2 := by
    have he := congrArg (coeff 5) hA
    norm_num [h, coeff_subst_range _ _ h0, coeff_h389472_pow, Nat.choose, Finset.sum_range_succ,
      coeff_X_pow_mul', ha0, ha1, ha2] at he
    omega
  have ha4 : coeff 4 A = 3 := by
    have he := congrArg (coeff 6) hA
    norm_num [h, coeff_subst_range _ _ h0, coeff_h389472_pow, Nat.choose, Finset.sum_range_succ,
      coeff_X_pow_mul', ha0, ha1, ha2, ha3] at he
    omega
  have ha5 : coeff 5 A = 6 := by
    have he := congrArg (coeff 7) hA
    norm_num [h, coeff_subst_range _ _ h0, coeff_h389472_pow, Nat.choose, Finset.sum_range_succ,
      coeff_X_pow_mul', ha0, ha1, ha2, ha3, ha4] at he
    omega
  have ha6 : coeff 6 A = 9 := by
    have he := congrArg (coeff 8) hA
    norm_num [h, coeff_subst_range _ _ h0, coeff_h389472_pow, Nat.choose, Finset.sum_range_succ,
      coeff_X_pow_mul', ha0, ha1, ha2, ha3, ha4, ha5] at he
    omega
  exact ⟨ha0, ha1, ha3, ha4, ha5, ha6⟩

theorem check_DATA_A301933 : DATA_A301933 := by
  intro A h0 hA
  change A * (1 + A * derivative (R := ℤ) A) = X * (1 + 4 * A * derivative (R := ℤ) A) at hA
  have ha0 : coeff 0 A = 0 := by simpa only [coeff_zero_eq_constantCoeff_apply] using h0
  have p2_0 : coeff 0 (A ^ 2) = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0]
  have ha1 : coeff 1 A = 1 := by
    have he := congrArg (coeff 1) hA
    norm_num [coeff_mul_range, Finset.sum_range_succ, coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_derivative, ha0, p2_0] at he
    nlinarith [he]
  have p2_1 : coeff 1 (A ^ 2) = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0]
  have ha2 : coeff 2 A = 3 := by
    have he := congrArg (coeff 2) hA
    norm_num [coeff_mul_range, Finset.sum_range_succ, coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_derivative, ha0, ha1, p2_0, p2_1] at he
    nlinarith [he]
  have p2_2 : coeff 2 (A ^ 2) = 1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p2_0, p2_1]
  have ha3 : coeff 3 A = 24 := by
    have he := congrArg (coeff 3) hA
    norm_num [coeff_mul_range, Finset.sum_range_succ, coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_derivative, ha0, ha1, ha2, p2_0, p2_1, p2_2] at he
    nlinarith [he]
  have p2_3 : coeff 3 (A ^ 2) = 6 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p2_0, p2_1, p2_2]
  have ha4 : coeff 4 A = 291 := by
    have he := congrArg (coeff 4) hA
    norm_num [coeff_mul_range, Finset.sum_range_succ, coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_derivative, ha0, ha1, ha2, ha3, p2_0, p2_1, p2_2, p2_3] at he
    nlinarith [he]
  have p2_4 : coeff 4 (A ^ 2) = 57 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p2_0, p2_1, p2_2, p2_3]
  have ha5 : coeff 5 A = 4596 := by
    have he := congrArg (coeff 5) hA
    norm_num [coeff_mul_range, Finset.sum_range_succ, coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_derivative, ha0, ha1, ha2, ha3, ha4, p2_0, p2_1, p2_2, p2_3, p2_4] at he
    nlinarith [he]
  exact ⟨ha1, ha2, ha3, ha4, ha5⟩

theorem check_DATA_A388734 : DATA_A388734 := by
  intro A hA
  change A = 1 + X * A ^ 2 + X ^ 2 * (1 - X) * A ^ 3 at hA
  have ha0 : coeff 0 A = 1 := by
    have he := congrArg constantCoeff hA
    simpa only [coeff_zero_eq_constantCoeff_apply, map_add, map_mul, map_one, map_sub, map_pow, constantCoeff_X, zero_mul, zero_pow two_ne_zero, zero_add, add_zero] using he
  have p2_0 : coeff 0 (A ^ 2) = 1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0]
  have p3_0 : coeff 0 (A ^ 3) = 1 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, p2_0]
  have ha1 : coeff 1 A = 1 := by
    have he := congrArg (coeff 1) hA
    norm_num [coeff_mul_range, Finset.sum_range_succ, coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_derivative, ha0, p2_0, p3_0] at he
    nlinarith [he]
  have p2_1 : coeff 1 (A ^ 2) = 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0]
  have p3_1 : coeff 1 (A ^ 3) = 3 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, p2_0, p2_1, p3_0]
  have ha2 : coeff 2 A = 3 := by
    have he := congrArg (coeff 2) hA
    norm_num [coeff_mul_range, Finset.sum_range_succ, coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_derivative, ha0, ha1, p2_0, p2_1, p3_0, p3_1] at he
    nlinarith [he]
  have p2_2 : coeff 2 (A ^ 2) = 7 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p2_0, p2_1]
  have p3_2 : coeff 2 (A ^ 3) = 12 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, p2_0, p2_1, p2_2, p3_0, p3_1]
  have ha3 : coeff 3 A = 9 := by
    have he := congrArg (coeff 3) hA
    norm_num [coeff_mul_range, Finset.sum_range_succ, coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_derivative, ha0, ha1, ha2, p2_0, p2_1, p2_2, p3_0, p3_1, p3_2] at he
    nlinarith [he]
  have p2_3 : coeff 3 (A ^ 2) = 24 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p2_0, p2_1, p2_2]
  have p3_3 : coeff 3 (A ^ 3) = 46 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, p2_0, p2_1, p2_2, p2_3, p3_0, p3_1, p3_2]
  have ha4 : coeff 4 A = 33 := by
    have he := congrArg (coeff 4) hA
    norm_num [coeff_mul_range, Finset.sum_range_succ, coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_derivative, ha0, ha1, ha2, ha3, p2_0, p2_1, p2_2, p2_3, p3_0, p3_1, p3_2, p3_3] at he
    nlinarith [he]
  have p2_4 : coeff 4 (A ^ 2) = 93 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p2_0, p2_1, p2_2, p2_3]
  have p3_4 : coeff 4 (A ^ 3) = 189 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, coeff_mul_range]
    norm_num [Finset.sum_range_succ, pow_one, ha0, ha1, ha2, ha3, ha4, p2_0, p2_1, p2_2, p2_3, p2_4, p3_0, p3_1, p3_2, p3_3]
  have ha5 : coeff 5 A = 127 := by
    have he := congrArg (coeff 5) hA
    norm_num [coeff_mul_range, Finset.sum_range_succ, coeff_X_pow_mul', coeff_X, coeff_X_pow, coeff_derivative, ha0, ha1, ha2, ha3, ha4, p2_0, p2_1, p2_2, p2_3, p2_4, p3_0, p3_1, p3_2, p3_3, p3_4] at he
    nlinarith [he]
  exact ⟨ha0, ha1, ha2, ha3, ha4, ha5⟩

end BackfillPaper2.DataEquations
#print axioms BackfillPaper2.DataEquations.check_DATA_A389472
#print axioms BackfillPaper2.DataEquations.check_DATA_A301933
#print axioms BackfillPaper2.DataEquations.check_DATA_A388734
