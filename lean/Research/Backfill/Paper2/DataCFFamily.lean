import Research.Backfill.Paper2.Challenge

/-! Exact finite coefficient extraction from every original signed tail solution. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.DataCFFamily
open PowerSeries BackfillPaper2.Challenge

private theorem cm (F G : PowerSeries ℤ) (n : ℕ) :
    coeff n (F * G) = ∑ j ∈ Finset.range (n + 1), coeff j F * coeff (n - j) G := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private theorem values (e : ℕ) (A : PowerSeries ℤ) (T : ℕ → PowerSeries ℤ) (h : CF e A T) :
    constantCoeff A = 1 ∧ coeff 1 A = 1 ∧
      coeff 2 A = (2 : ℤ) ^ e - 1 ∧
      coeff 3 A = ((2 : ℤ) ^ e) ^ 2 + (2 : ℤ) ^ e * (3 : ℤ) ^ e - 4 * (2 : ℤ) ^ e + 2 ∧
      coeff 4 A = ((2 : ℤ) ^ e) ^ 3 + 2 * ((2 : ℤ) ^ e) ^ 2 * (3 : ℤ) ^ e -
        9 * ((2 : ℤ) ^ e) ^ 2 - 6 * (2 : ℤ) ^ e * (3 : ℤ) ^ e + 15 * (2 : ℤ) ^ e - 5 +
        (2 : ℤ) ^ e * ((3 : ℤ) ^ e) ^ 2 + (2 : ℤ) ^ e * (3 : ℤ) ^ e * (4 : ℤ) ^ e := by
  have hne : ∀ k, constantCoeff (T k) ≠ 0 := by
    intro k
    rcases h.1 k with he | he <;> rw [he] <;> norm_num
  have ha0 : constantCoeff A = 1 := by
    have he := congrArg constantCoeff h.2.1
    simp only [map_mul, map_sub, map_one, constantCoeff_X] at he
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (hne 0))
  have ht0 : ∀ k, constantCoeff (T k) = 1 := by
    intro k
    have he := congrArg constantCoeff (h.2.2 k)
    simp only [map_mul, map_sub, constantCoeff_C, constantCoeff_X, mul_zero] at he
    have hh := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (hne (k + 1)))
    exact hh.symm.trans ha0
  have ha1 : coeff 1 A = 1 := by
    have he := congrArg (coeff 1) h.2.1
    norm_num [coeff_X, coeff_C, map_ofNat, cm, Finset.sum_range_succ, coeff_zero_eq_constantCoeff_apply, ha0, ht0] at he
    exact he
  have ht1 : ∀ k, coeff 1 (T k) = 1 - ((k : ℤ) + 2) ^ e := by
    intro k
    have he := congrArg (coeff 1) (h.2.2 k)
    rw [coeff_C_mul] at he
    norm_num [coeff_X, coeff_C, map_ofNat, cm, Finset.sum_range_succ, coeff_zero_eq_constantCoeff_apply, ha0, ht0, ha1] at he
    linear_combination -he
  have ha2 : coeff 2 A = (2 : ℤ) ^ e - 1 := by
    have he := congrArg (coeff 2) h.2.1
    norm_num [coeff_X, coeff_C, map_ofNat, cm, Finset.sum_range_succ, coeff_zero_eq_constantCoeff_apply, ha0, ht0, ha1, ht1] at he
    linear_combination he
  have ht2 : ∀ k, coeff 2 (T k) = (2 : ℤ) ^ e - 1 +
      (((k : ℤ) + 2) ^ e) * (1 - ((k : ℤ) + 3) ^ e) := by
    intro k
    have he := congrArg (coeff 2) (h.2.2 k)
    rw [coeff_C_mul] at he
    norm_num [coeff_X, coeff_C, map_ofNat, cm, Finset.sum_range_succ, coeff_zero_eq_constantCoeff_apply, ha0, ht0, ha1, ha2, ht1,
      Nat.cast_add, Nat.cast_one] at he
    linear_combination -he
  have ha3 : coeff 3 A = ((2 : ℤ) ^ e) ^ 2 + (2 : ℤ) ^ e * (3 : ℤ) ^ e - 4 * (2 : ℤ) ^ e + 2 := by
    have he := congrArg (coeff 3) h.2.1
    norm_num [coeff_X, coeff_C, map_ofNat, cm, Finset.sum_range_succ, coeff_zero_eq_constantCoeff_apply, ha0, ht0, ha1, ha2, ht1, ht2] at he
    linear_combination he
  have ht3 : coeff 3 (T 0) = 2 * ((2 : ℤ) ^ e) ^ 2 +
      4 * (2 : ℤ) ^ e * (3 : ℤ) ^ e - 6 * (2 : ℤ) ^ e + 2 -
      (2 : ℤ) ^ e * ((3 : ℤ) ^ e) ^ 2 - (2 : ℤ) ^ e * (3 : ℤ) ^ e * (4 : ℤ) ^ e := by
    have he := congrArg (coeff 3) (h.2.2 0)
    rw [coeff_C_mul] at he
    norm_num [coeff_X, coeff_C, map_ofNat, cm, Finset.sum_range_succ, coeff_zero_eq_constantCoeff_apply, ha0, ht0, ha1, ha2, ha3, ht1, ht2] at he
    linear_combination -he
  refine ⟨ha0, ha1, ha2, ha3, ?_⟩
  have he := congrArg (coeff 4) h.2.1
  norm_num [coeff_X, coeff_C, map_ofNat, cm, Finset.sum_range_succ, coeff_zero_eq_constantCoeff_apply, ha0, ht0, ha1, ha2, ha3, ht1, ht2, ht3] at he
  linear_combination he

theorem check_DATA_A338633 : DATA_A338633 := by
  intro A T h
  have he := values 3 A T h
  norm_num at he
  exact ⟨by simpa only [coeff_zero_eq_constantCoeff_apply] using he.1, he.2⟩

theorem check_DATA_A338634 : DATA_A338634 := by
  intro A T h
  have he := values 4 A T h
  norm_num at he
  exact ⟨by simpa only [coeff_zero_eq_constantCoeff_apply] using he.1, he.2⟩

end BackfillPaper2.DataCFFamily
#print axioms BackfillPaper2.DataCFFamily.check_DATA_A338633
#print axioms BackfillPaper2.DataCFFamily.check_DATA_A338634
