import Research.Backfill.Paper2.FiniteCoefficients

/-! Exact finite original DATA gates. Each claimed table value is a Lean proof obligation. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.DataAlgebraic
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.FiniteCoefficients

private theorem a240998_ha1 (A : PowerSeries ℤ) (hA : Eq240998 A) (ha0 : coeff 0 A = 1) : coeff 1 A = 1 := by
  let h : PowerSeries ℤ := X + 2 * X ^ 2
  have hh0 : constantCoeff h = 0 := by simp [h]
  change A ^ 2 = X + A.subst h at hA
  have he := congrArg (coeff 1) hA
  rw [map_add, coeff_subst_range A h hh0] at he
  norm_num [h, pow_succ, coeff_mul_range, Finset.sum_range_succ, coeff_X, coeff_X_pow, ha0] at he
  nlinarith [he]

private theorem a240998_ha2 (A : PowerSeries ℤ) (hA : Eq240998 A) (ha0 : coeff 0 A = 1) (ha1 : coeff 1 A = 1) : coeff 2 A = 1 := by
  let h : PowerSeries ℤ := X + 2 * X ^ 2
  have hh0 : constantCoeff h = 0 := by simp [h]
  change A ^ 2 = X + A.subst h at hA
  have he := congrArg (coeff 2) hA
  rw [map_add, coeff_subst_range A h hh0] at he
  norm_num [h, pow_succ, coeff_mul_range, Finset.sum_range_succ, coeff_X, coeff_X_pow, ha0, ha1] at he
  nlinarith [he]

private theorem a240998_ha3 (A : PowerSeries ℤ) (hA : Eq240998 A) (ha0 : coeff 0 A = 1) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 1) : coeff 3 A = 2 := by
  let h : PowerSeries ℤ := X + 2 * X ^ 2
  have hh0 : constantCoeff h = 0 := by simp [h]
  change A ^ 2 = X + A.subst h at hA
  have he := congrArg (coeff 3) hA
  rw [map_add, coeff_subst_range A h hh0] at he
  norm_num [h, pow_succ, coeff_mul_range, Finset.sum_range_succ, coeff_X, coeff_X_pow, ha0, ha1, ha2] at he
  nlinarith [he]

private theorem a240998_ha4 (A : PowerSeries ℤ) (hA : Eq240998 A) (ha0 : coeff 0 A = 1) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 1) (ha3 : coeff 3 A = 2) : coeff 4 A = 11 := by
  let h : PowerSeries ℤ := X + 2 * X ^ 2
  have hh0 : constantCoeff h = 0 := by simp [h]
  change A ^ 2 = X + A.subst h at hA
  have he := congrArg (coeff 4) hA
  rw [map_add, coeff_subst_range A h hh0] at he
  norm_num [h, pow_succ, coeff_mul_range, Finset.sum_range_succ, coeff_X, coeff_X_pow, ha0, ha1, ha2, ha3] at he
  nlinarith [he]

private theorem a240998_ha5 (A : PowerSeries ℤ) (hA : Eq240998 A) (ha0 : coeff 0 A = 1) (ha1 : coeff 1 A = 1) (ha2 : coeff 2 A = 1) (ha3 : coeff 3 A = 2) (ha4 : coeff 4 A = 11) : coeff 5 A = 86 := by
  let h : PowerSeries ℤ := X + 2 * X ^ 2
  have hh0 : constantCoeff h = 0 := by simp [h]
  change A ^ 2 = X + A.subst h at hA
  have he := congrArg (coeff 5) hA
  rw [map_add, coeff_subst_range A h hh0] at he
  norm_num [h, pow_succ, coeff_mul_range, Finset.sum_range_succ, coeff_X, coeff_X_pow, ha0, ha1, ha2, ha3, ha4] at he
  nlinarith [he]

theorem check_DATA_A240998 : DATA_A240998 := by
  intro A h0 hA
  have ha0 : coeff 0 A = 1 := by simpa only [coeff_zero_eq_constantCoeff_apply] using h0
  have ha1 : coeff 1 A = 1 := a240998_ha1 A hA ha0
  have ha2 : coeff 2 A = 1 := a240998_ha2 A hA ha0 ha1
  have ha3 : coeff 3 A = 2 := a240998_ha3 A hA ha0 ha1 ha2
  have ha4 : coeff 4 A = 11 := a240998_ha4 A hA ha0 ha1 ha2 ha3
  have ha5 : coeff 5 A = 86 := a240998_ha5 A hA ha0 ha1 ha2 ha3 ha4
  exact ⟨ha1, ha2, ha3, ha4, ha5⟩

theorem check_DATA_A273958 : DATA_A273958 := by
  intro S A hA
  obtain ⟨hS, hA⟩ := hA
  have hs0 : coeff 0 S = 0 := by
    have he := congrArg constantCoeff hA
    simp only [map_add, map_mul, map_pow, constantCoeff_X, zero_pow two_ne_zero,
      zero_mul, zero_add] at he
    have hz : constantCoeff S = 0 := by nlinarith [sq_nonneg (constantCoeff S)]
    simpa only [coeff_zero_eq_constantCoeff_apply] using hz
  have hs1 : coeff 1 S = 1 := by
    have he := congrArg (coeff 1) hS
    norm_num [pow_two, coeff_mul_range, Finset.sum_range_succ, coeff_X, hs0] at he
    nlinarith [he]
  have hs2 : coeff 2 S = 1 := by
    have he := congrArg (coeff 2) hS
    norm_num [pow_two, coeff_mul_range, Finset.sum_range_succ, coeff_X, hs0, hs1] at he
    nlinarith [he]
  have hs3 : coeff 3 S = 2 := by
    have he := congrArg (coeff 3) hS
    norm_num [pow_two, coeff_mul_range, Finset.sum_range_succ, coeff_X, hs0, hs1, hs2] at he
    nlinarith [he]
  have hs4 : coeff 4 S = 5 := by
    have he := congrArg (coeff 4) hS
    norm_num [pow_two, coeff_mul_range, Finset.sum_range_succ, coeff_X, hs0, hs1, hs2, hs3] at he
    nlinarith [he]
  have hs5 : coeff 5 S = 14 := by
    have he := congrArg (coeff 5) hS
    norm_num [pow_two, coeff_mul_range, Finset.sum_range_succ, coeff_X, hs0, hs1, hs2, hs3, hs4] at he
    nlinarith [he]
  have hs6 : coeff 6 S = 42 := by
    have he := congrArg (coeff 6) hS
    norm_num [pow_two, coeff_mul_range, Finset.sum_range_succ, coeff_X, hs0, hs1, hs2, hs3, hs4, hs5] at he
    nlinarith [he]
  have ha0 : coeff 0 A = 0 := by
    have he := congrArg (coeff 1) hA
    norm_num [pow_two, coeff_mul_range, coeff_X_pow_mul', coeff_X, coeff_X_pow, Finset.sum_range_succ, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at he
    simpa only [coeff_zero_eq_constantCoeff_apply] using he
  have ha1 : coeff 1 A = 1 := by
    have he := congrArg (coeff 2) hA
    norm_num [pow_two, coeff_mul_range, coeff_X_pow_mul', coeff_X, coeff_X_pow, Finset.sum_range_succ, hs0, hs1, hs2, hs3, hs4, hs5, hs6, ha0] at he
    nlinarith [he]
  have ha2 : coeff 2 A = 2 := by
    have he := congrArg (coeff 3) hA
    norm_num [pow_two, coeff_mul_range, coeff_X_pow_mul', coeff_X, coeff_X_pow, Finset.sum_range_succ, hs0, hs1, hs2, hs3, hs4, hs5, hs6, ha0, ha1] at he
    nlinarith [he]
  have ha3 : coeff 3 A = 4 := by
    have he := congrArg (coeff 4) hA
    norm_num [pow_two, coeff_mul_range, coeff_X_pow_mul', coeff_X, coeff_X_pow, Finset.sum_range_succ, hs0, hs1, hs2, hs3, hs4, hs5, hs6, ha0, ha1, ha2] at he
    nlinarith [he]
  have ha4 : coeff 4 A = 10 := by
    have he := congrArg (coeff 5) hA
    norm_num [pow_two, coeff_mul_range, coeff_X_pow_mul', coeff_X, coeff_X_pow, Finset.sum_range_succ, hs0, hs1, hs2, hs3, hs4, hs5, hs6, ha0, ha1, ha2, ha3] at he
    nlinarith [he]
  have ha5 : coeff 5 A = 30 := by
    have he := congrArg (coeff 6) hA
    norm_num [pow_two, coeff_mul_range, coeff_X_pow_mul', coeff_X, coeff_X_pow, Finset.sum_range_succ, hs0, hs1, hs2, hs3, hs4, hs5, hs6, ha0, ha1, ha2, ha3, ha4] at he
    nlinarith [he]
  exact ⟨ha0, ha1, ha2, ha3, ha4, ha5⟩

end BackfillPaper2.DataAlgebraic
#print axioms BackfillPaper2.DataAlgebraic.check_DATA_A240998
#print axioms BackfillPaper2.DataAlgebraic.check_DATA_A273958
