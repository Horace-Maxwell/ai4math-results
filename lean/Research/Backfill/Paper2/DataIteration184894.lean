import Research.Backfill.Paper2.FiniteCoefficients

/-! Finite exact convolution certificates for every original normalized solution. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.DataIteration184894
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.FiniteCoefficients

private theorem cm (F G : Polynomial ℤ) (n : ℕ) :
    (F * G).coeff n = ∑ j ∈ Finset.range (n + 1), F.coeff j * G.coeff (n - j) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

private theorem a0_0 : (P184894 0).coeff 0 = 0 := by
  norm_num [P184894, Polynomial.coeff_X]

private theorem a0_1 : (P184894 0).coeff 1 = 1 := by
  norm_num [P184894, Polynomial.coeff_X]

private theorem a0_2 : (P184894 0).coeff 2 = 0 := by
  norm_num [P184894, Polynomial.coeff_X]

private theorem a0_3 : (P184894 0).coeff 3 = 0 := by
  norm_num [P184894, Polynomial.coeff_X]

private theorem a0_4 : (P184894 0).coeff 4 = 0 := by
  norm_num [P184894, Polynomial.coeff_X]

private theorem a0_5 : (P184894 0).coeff 5 = 0 := by
  norm_num [P184894, Polynomial.coeff_X]

private theorem a0_6 : (P184894 0).coeff 6 = 0 := by
  norm_num [P184894, Polynomial.coeff_X]

private theorem a0_7 : (P184894 0).coeff 7 = 0 := by
  norm_num [P184894, Polynomial.coeff_X]

private theorem a0_8 : (P184894 0).coeff 8 = 0 := by
  norm_num [P184894, Polynomial.coeff_X]

private theorem a0_9 : (P184894 0).coeff 9 = 0 := by
  norm_num [P184894, Polynomial.coeff_X]

private theorem a1_0 : (P184894 1).coeff 0 = 0 := by
  rw [show 1 = 0 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a0_0]

private theorem a1_1 : (P184894 1).coeff 1 = 1 := by
  rw [show 1 = 0 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a0_0, a0_1]

private theorem a1_2 : (P184894 1).coeff 2 = 0 := by
  rw [show 1 = 0 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a0_0, a0_1, a0_2]

private theorem a1_3 : (P184894 1).coeff 3 = 1 := by
  rw [show 1 = 0 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a0_0, a0_1, a0_2, a0_3]

private theorem a1_4 : (P184894 1).coeff 4 = 0 := by
  rw [show 1 = 0 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a0_0, a0_1, a0_2, a0_3, a0_4]

private theorem a1_5 : (P184894 1).coeff 5 = 0 := by
  rw [show 1 = 0 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a0_0, a0_1, a0_2, a0_3, a0_4, a0_5]

private theorem a1_6 : (P184894 1).coeff 6 = 0 := by
  rw [show 1 = 0 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a0_0, a0_1, a0_2, a0_3, a0_4, a0_5, a0_6]

private theorem a1_7 : (P184894 1).coeff 7 = 0 := by
  rw [show 1 = 0 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a0_0, a0_1, a0_2, a0_3, a0_4, a0_5, a0_6, a0_7]

private theorem a1_8 : (P184894 1).coeff 8 = 0 := by
  rw [show 1 = 0 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a0_0, a0_1, a0_2, a0_3, a0_4, a0_5, a0_6, a0_7, a0_8]

private theorem a1_9 : (P184894 1).coeff 9 = 0 := by
  rw [show 1 = 0 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a0_0, a0_1, a0_2, a0_3, a0_4, a0_5, a0_6, a0_7, a0_8, a0_9]

private theorem a2_0 : (P184894 2).coeff 0 = 0 := by
  rw [show 2 = 1 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a1_0]

private theorem a2_1 : (P184894 2).coeff 1 = 1 := by
  rw [show 2 = 1 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a1_0, a1_1]

private theorem a2_2 : (P184894 2).coeff 2 = 0 := by
  rw [show 2 = 1 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a1_0, a1_1, a1_2]

private theorem a2_3 : (P184894 2).coeff 3 = 2 := by
  rw [show 2 = 1 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a1_0, a1_1, a1_2, a1_3]

private theorem a2_4 : (P184894 2).coeff 4 = 0 := by
  rw [show 2 = 1 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a1_0, a1_1, a1_2, a1_3, a1_4]

private theorem a2_5 : (P184894 2).coeff 5 = 3 := by
  rw [show 2 = 1 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a1_0, a1_1, a1_2, a1_3, a1_4, a1_5]

private theorem a2_6 : (P184894 2).coeff 6 = 0 := by
  rw [show 2 = 1 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a1_0, a1_1, a1_2, a1_3, a1_4, a1_5, a1_6]

private theorem a2_7 : (P184894 2).coeff 7 = 3 := by
  rw [show 2 = 1 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a1_0, a1_1, a1_2, a1_3, a1_4, a1_5, a1_6, a1_7]

private theorem a2_8 : (P184894 2).coeff 8 = 0 := by
  rw [show 2 = 1 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a1_0, a1_1, a1_2, a1_3, a1_4, a1_5, a1_6, a1_7, a1_8]

private theorem a2_9 : (P184894 2).coeff 9 = 1 := by
  rw [show 2 = 1 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a1_0, a1_1, a1_2, a1_3, a1_4, a1_5, a1_6, a1_7, a1_8, a1_9]

private theorem a3_0 : (P184894 3).coeff 0 = 0 := by
  rw [show 3 = 2 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a2_0]

private theorem a3_1 : (P184894 3).coeff 1 = 1 := by
  rw [show 3 = 2 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a2_0, a2_1]

private theorem a3_2 : (P184894 3).coeff 2 = 0 := by
  rw [show 3 = 2 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a2_0, a2_1, a2_2]

private theorem a3_3 : (P184894 3).coeff 3 = 3 := by
  rw [show 3 = 2 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a2_0, a2_1, a2_2, a2_3]

private theorem a3_4 : (P184894 3).coeff 4 = 0 := by
  rw [show 3 = 2 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a2_0, a2_1, a2_2, a2_3, a2_4]

private theorem a3_5 : (P184894 3).coeff 5 = 9 := by
  rw [show 3 = 2 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a2_0, a2_1, a2_2, a2_3, a2_4, a2_5]

private theorem a3_6 : (P184894 3).coeff 6 = 0 := by
  rw [show 3 = 2 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a2_0, a2_1, a2_2, a2_3, a2_4, a2_5, a2_6]

private theorem a3_7 : (P184894 3).coeff 7 = 24 := by
  rw [show 3 = 2 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a2_0, a2_1, a2_2, a2_3, a2_4, a2_5, a2_6, a2_7]

private theorem a3_8 : (P184894 3).coeff 8 = 0 := by
  rw [show 3 = 2 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a2_0, a2_1, a2_2, a2_3, a2_4, a2_5, a2_6, a2_7, a2_8]

private theorem a3_9 : (P184894 3).coeff 9 = 54 := by
  rw [show 3 = 2 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a2_0, a2_1, a2_2, a2_3, a2_4, a2_5, a2_6, a2_7, a2_8, a2_9]

private theorem a4_0 : (P184894 4).coeff 0 = 0 := by
  rw [show 4 = 3 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a3_0]

private theorem a4_1 : (P184894 4).coeff 1 = 1 := by
  rw [show 4 = 3 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a3_0, a3_1]

private theorem a4_2 : (P184894 4).coeff 2 = 0 := by
  rw [show 4 = 3 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a3_0, a3_1, a3_2]

private theorem a4_3 : (P184894 4).coeff 3 = 4 := by
  rw [show 4 = 3 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a3_0, a3_1, a3_2, a3_3]

private theorem a4_4 : (P184894 4).coeff 4 = 0 := by
  rw [show 4 = 3 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a3_0, a3_1, a3_2, a3_3, a3_4]

private theorem a4_5 : (P184894 4).coeff 5 = 18 := by
  rw [show 4 = 3 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a3_0, a3_1, a3_2, a3_3, a3_4, a3_5]

private theorem a4_6 : (P184894 4).coeff 6 = 0 := by
  rw [show 4 = 3 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a3_0, a3_1, a3_2, a3_3, a3_4, a3_5, a3_6]

private theorem a4_7 : (P184894 4).coeff 7 = 78 := by
  rw [show 4 = 3 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a3_0, a3_1, a3_2, a3_3, a3_4, a3_5, a3_6, a3_7]

private theorem a4_8 : (P184894 4).coeff 8 = 0 := by
  rw [show 4 = 3 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a3_0, a3_1, a3_2, a3_3, a3_4, a3_5, a3_6, a3_7, a3_8]

private theorem a4_9 : (P184894 4).coeff 9 = 315 := by
  rw [show 4 = 3 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a3_0, a3_1, a3_2, a3_3, a3_4, a3_5, a3_6, a3_7, a3_8, a3_9]

private theorem a5_0 : (P184894 5).coeff 0 = 0 := by
  rw [show 5 = 4 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a4_0]

private theorem a5_1 : (P184894 5).coeff 1 = 1 := by
  rw [show 5 = 4 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a4_0, a4_1]

private theorem a5_2 : (P184894 5).coeff 2 = 0 := by
  rw [show 5 = 4 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a4_0, a4_1, a4_2]

private theorem a5_3 : (P184894 5).coeff 3 = 5 := by
  rw [show 5 = 4 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a4_0, a4_1, a4_2, a4_3]

private theorem a5_4 : (P184894 5).coeff 4 = 0 := by
  rw [show 5 = 4 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a4_0, a4_1, a4_2, a4_3, a4_4]

private theorem a5_5 : (P184894 5).coeff 5 = 30 := by
  rw [show 5 = 4 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a4_0, a4_1, a4_2, a4_3, a4_4, a4_5]

private theorem a5_6 : (P184894 5).coeff 6 = 0 := by
  rw [show 5 = 4 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a4_0, a4_1, a4_2, a4_3, a4_4, a4_5, a4_6]

private theorem a5_7 : (P184894 5).coeff 7 = 180 := by
  rw [show 5 = 4 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a4_0, a4_1, a4_2, a4_3, a4_4, a4_5, a4_6, a4_7]

private theorem a5_8 : (P184894 5).coeff 8 = 0 := by
  rw [show 5 = 4 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a4_0, a4_1, a4_2, a4_3, a4_4, a4_5, a4_6, a4_7, a4_8]

private theorem a5_9 : (P184894 5).coeff 9 = 1045 := by
  rw [show 5 = 4 + 1 from rfl, P184894]
  norm_num [Polynomial.coeff_add, pow_succ, cm, Finset.sum_range_succ, a4_0, a4_1, a4_2, a4_3, a4_4, a4_5, a4_6, a4_7, a4_8, a4_9]

theorem check_DATA_A184894 : DATA_A184894 := by
  simpa only [DATA_A184894, a184894, Nat.reduceMul, Nat.reduceSub] using
    (show (P184894 1).coeff 1 = 1 ∧ (P184894 2).coeff 3 = 2 ∧ (P184894 3).coeff 5 = 9 ∧ (P184894 4).coeff 7 = 78 ∧ (P184894 5).coeff 9 = 1045 from
      ⟨a1_1, a2_3, a3_5, a4_7, a5_9⟩)

end BackfillPaper2.DataIteration184894
#print axioms BackfillPaper2.DataIteration184894.check_DATA_A184894
