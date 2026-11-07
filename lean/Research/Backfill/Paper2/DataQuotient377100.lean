import Research.Backfill.Paper2.FiniteCoefficients

/-! Exact finite original DATA gates. Each claimed table value is a Lean proof obligation. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.DataQuotient377100
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.FiniteCoefficients

theorem check_DATA_A377100 : DATA_A377100 := by
  intro A U h0 h1 hA
  have hu : U = A - A ^ 2 := by linear_combination -hA.2
  have hEq := hA.1
  rw [hu, show A ^ 2 = A * A by ring] at hEq
  have ha0 : coeff 0 A = 0 := by simpa only [coeff_zero_eq_constantCoeff_apply] using h0
  have ha1 : coeff 1 A = 1 := h1
  have ha2 : coeff 2 A = 1 := by
    have he := congrArg (coeff 4) hEq
    norm_num [constantCoeff_subst_X_pow two_ne_zero, coeff_mul_range, coeff_subst_X_pow two_ne_zero, coeff_subst_X_pow three_ne_zero, Finset.sum_range_succ, ha0, ha1] at he
    nlinarith [he]
  have ha3 : coeff 3 A = 1 := by
    have he := congrArg (coeff 5) hEq
    norm_num [constantCoeff_subst_X_pow two_ne_zero, coeff_mul_range, coeff_subst_X_pow two_ne_zero, coeff_subst_X_pow three_ne_zero, Finset.sum_range_succ, ha0, ha1, ha2] at he
    nlinarith [he]
  have ha4 : coeff 4 A = 4 := by
    have he := congrArg (coeff 6) hEq
    norm_num [constantCoeff_subst_X_pow two_ne_zero, coeff_mul_range, coeff_subst_X_pow two_ne_zero, coeff_subst_X_pow three_ne_zero, Finset.sum_range_succ, ha0, ha1, ha2, ha3] at he
    nlinarith [he]
  have ha5 : coeff 5 A = 10 := by
    have he := congrArg (coeff 7) hEq
    norm_num [constantCoeff_subst_X_pow two_ne_zero, coeff_mul_range, coeff_subst_X_pow two_ne_zero, coeff_subst_X_pow three_ne_zero, Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4] at he
    nlinarith [he]
  have ha6 : coeff 6 A = 28 := by
    have he := congrArg (coeff 8) hEq
    norm_num [constantCoeff_subst_X_pow two_ne_zero, coeff_mul_range, coeff_subst_X_pow two_ne_zero, coeff_subst_X_pow three_ne_zero, Finset.sum_range_succ, ha0, ha1, ha2, ha3, ha4, ha5] at he
    nlinarith [he]
  exact ⟨ha2, ha3, ha4, ha5, ha6⟩

end BackfillPaper2.DataQuotient377100
#print axioms BackfillPaper2.DataQuotient377100.check_DATA_A377100
