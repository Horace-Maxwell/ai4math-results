import Research.Backfill.Paper7.BMS32SixDet

/-! Source-only repair: independent small determinant declarations replace
the former all-five-cases six-by-six expansion. Default budgets are retained. -/
set_option autoImplicit false
namespace Paper7C61TwoSiteDet
open scoped Matrix

def nearCore (a b : ℤ) : Matrix (Fin 6) (Fin 6) ℤ :=
  !![-2,-2,0,0,0,-2;
     -2,a,-2,0,0,0;
     0,-2,b,-2,0,0;
     0,0,-2,4,-2,0;
     0,0,0,-2,4,-2;
     -2,0,0,0,-2,4]
#print axioms Paper7C61TwoSiteDet.nearCore

def minorZero (a b : ℤ) : Matrix (Fin 5) (Fin 5) ℤ :=
  !![a,-2,0,0,0;
     -2,b,-2,0,0;
     0,-2,4,-2,0;
     0,0,-2,4,-2;
     0,0,0,-2,4]
#print axioms Paper7C61TwoSiteDet.minorZero

def minorOne (b : ℤ) : Matrix (Fin 5) (Fin 5) ℤ :=
  !![-2,-2,0,0,0;
     0,b,-2,0,0;
     0,-2,4,-2,0;
     0,0,-2,4,-2;
     -2,0,0,-2,4]
#print axioms Paper7C61TwoSiteDet.minorOne

def minorFive (a b : ℤ) : Matrix (Fin 5) (Fin 5) ℤ :=
  !![-2,a,-2,0,0;
     0,-2,b,-2,0;
     0,0,-2,4,-2;
     0,0,0,-2,4;
     -2,0,0,0,-2]
#print axioms Paper7C61TwoSiteDet.minorFive

theorem nearCore_minor_zero (a b : ℤ) :
    (nearCore a b).submatrix Fin.succ (Fin.succAbove (0 : Fin 6)) = minorZero a b := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl
#print axioms Paper7C61TwoSiteDet.nearCore_minor_zero

theorem nearCore_minor_one (a b : ℤ) :
    (nearCore a b).submatrix Fin.succ (Fin.succAbove (1 : Fin 6)) = minorOne b := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl
#print axioms Paper7C61TwoSiteDet.nearCore_minor_one

theorem nearCore_minor_five (a b : ℤ) :
    (nearCore a b).submatrix Fin.succ (Fin.succAbove (5 : Fin 6)) = minorFive a b := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl
#print axioms Paper7C61TwoSiteDet.nearCore_minor_five

/-- Only the three nonzero entries of row zero contribute. The five-by-five
determinants stay opaque during this six-by-six expansion. -/
theorem nearCore_det (a b : ℤ) :
    (nearCore a b).det = -2 * (minorZero a b).det +
      2 * (minorOne b).det + 2 * (minorFive a b).det := by
  rw [Matrix.det_succ_row_zero]
  rw [Fin.sum_univ_six]
  rw [nearCore_minor_zero, nearCore_minor_one, nearCore_minor_five]
  norm_num [nearCore]
#print axioms Paper7C61TwoSiteDet.nearCore_det

theorem minorZero_one_four : (minorZero 1 4).det = -48 := by
  norm_num [minorZero, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
#print axioms Paper7C61TwoSiteDet.minorZero_one_four

theorem minorZero_four_one : (minorZero 4 1).det = -192 := by
  norm_num [minorZero, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
#print axioms Paper7C61TwoSiteDet.minorZero_four_one

theorem minorOne_four : (minorOne 4).det = -192 := by
  norm_num [minorOne, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
#print axioms Paper7C61TwoSiteDet.minorOne_four

theorem minorOne_one : (minorOne 1).det = 0 := by
  norm_num [minorOne, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
#print axioms Paper7C61TwoSiteDet.minorOne_one

theorem minorFive_one_four : (minorFive 1 4).det = 0 := by
  norm_num [minorFive, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
#print axioms Paper7C61TwoSiteDet.minorFive_one_four

theorem minorFive_four_one : (minorFive 4 1).det = 96 := by
  norm_num [minorFive, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
#print axioms Paper7C61TwoSiteDet.minorFive_four_one

theorem nearCore_one_four : (nearCore 1 4).det = -288 := by
  rw [nearCore_det, minorZero_one_four, minorOne_four, minorFive_one_four]
  norm_num
#print axioms Paper7C61TwoSiteDet.nearCore_one_four

theorem nearCore_four_one : (nearCore 4 1).det = 576 := by
  rw [nearCore_det, minorZero_four_one, minorOne_one, minorFive_four_one]
  norm_num
#print axioms Paper7C61TwoSiteDet.nearCore_four_one

def reflection : Fin 6 ≃ Fin 6 where
  toFun i := -i
  invFun i := -i
  left_inv i := by fin_cases i <;> decide
  right_inv i := by fin_cases i <;> decide
#print axioms Paper7C61TwoSiteDet.reflection

end Paper7C61TwoSiteDet
