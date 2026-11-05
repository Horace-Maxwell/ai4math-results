import Research.Backfill.Paper7.EightBinaryPathDet

/-! Three sparse cofactors reduce the cycle determinant to path determinants.
The two corner determinants are triangular and cancel in characteristic two. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open scoped Matrix BigOperators CharTwo

def binaryCycleMatrix {R : Type*} [Zero R] (a : Fin 8 → R) (x : R) :
    Matrix (Fin 8) (Fin 8) R :=
  !![a 0,x,0,0,0,0,0,x;
     x,a 1,x,0,0,0,0,0;
     0,x,a 2,x,0,0,0,0;
     0,0,x,a 3,x,0,0,0;
     0,0,0,x,a 4,x,0,0;
     0,0,0,0,x,a 5,x,0;
     0,0,0,0,0,x,a 6,x;
     x,0,0,0,0,0,x,a 7]
#print axioms Paper7EightCycle.binaryCycleMatrix

def binaryCycleCornerLow {R : Type*} [Zero R] (a : Fin 8 → R) (x : R) :
    Matrix (Fin 6) (Fin 6) R :=
  !![x,0,0,0,0,0;
     a 2,x,0,0,0,0;
     x,a 3,x,0,0,0;
     0,x,a 4,x,0,0;
     0,0,x,a 5,x,0;
     0,0,0,x,a 6,x]
#print axioms Paper7EightCycle.binaryCycleCornerLow

theorem binaryCycleCornerLow_det {R : Type*} [CommRing R]
    (a : Fin 8 → R) (x : R) : (binaryCycleCornerLow a x).det = x^6 := by
  have ht : (binaryCycleCornerLow a x).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;> norm_num [binaryCycleCornerLow] at *
  rw [Matrix.det_of_isLowerTriangular _ ht]
  norm_num [binaryCycleCornerLow, Fin.prod_univ_succ]
  all_goals ring
#print axioms Paper7EightCycle.binaryCycleCornerLow_det

theorem binary_cycle_minor_zero {R : Type*} [Zero R] (a : Fin 8 → R) (x : R) :
    (binaryCycleMatrix a x).submatrix Fin.succ (0 : Fin 8).succAbove =
      binaryPathMatrix 7 (fun i => a i.succ) x := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [binaryCycleMatrix, binaryPathMatrix, Matrix.submatrix, Fin.succAbove]
#print axioms Paper7EightCycle.binary_cycle_minor_zero

theorem binary_cycle_minor_one_det {R : Type*} [CommRing R] [CharP R 2]
    (a : Fin 8 → R) (x : R) :
    ((binaryCycleMatrix a x).submatrix Fin.succ (1 : Fin 8).succAbove).det =
      x * binaryPathDet 6 (fun i => a i.succ.succ) x + x^7 := by
  let B := (binaryCycleMatrix a x).submatrix Fin.succ (1 : Fin 8).succAbove
  have hcol (i : Fin 7) : B i 0 = ![x,0,0,0,0,0,x] i := by
    fin_cases i <;> norm_num [B, binaryCycleMatrix, Matrix.submatrix, Fin.succAbove]
  have hzero : B.submatrix Fin.succ Fin.succ =
      binaryPathMatrix 6 (fun i => a i.succ.succ) x := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, binaryCycleMatrix, binaryPathMatrix, Matrix.submatrix, Fin.succAbove]
  have hlast : B.submatrix (6 : Fin 7).succAbove Fin.succ =
      binaryCycleCornerLow a x := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, binaryCycleMatrix, binaryCycleCornerLow, Matrix.submatrix, Fin.succAbove]
  change B.det = _
  rw [Matrix.det_succ_column_zero]
  norm_num [Fin.sum_univ_succ, hcol, hzero, hlast, binaryCycleCornerLow_det,
    ← binaryPathDet_eq_det]
  all_goals ring
#print axioms Paper7EightCycle.binary_cycle_minor_one_det

theorem binary_cycle_minor_seven_det {R : Type*} [CommRing R] [CharP R 2]
    (a : Fin 8 → R) (x : R) :
    ((binaryCycleMatrix a x).submatrix Fin.succ (7 : Fin 8).succAbove).det =
      x^7 + x * binaryPathDet 6 (fun i => a i.succ.castSucc) x := by
  let B := (binaryCycleMatrix a x).submatrix Fin.succ (7 : Fin 8).succAbove
  have hcol (i : Fin 7) : B i 0 = ![x,0,0,0,0,0,x] i := by
    fin_cases i <;> norm_num [B, binaryCycleMatrix, Matrix.submatrix, Fin.succAbove]
  have hzero : B.submatrix Fin.succ Fin.succ =
      (binaryCycleCornerLow a x).transpose := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, binaryCycleMatrix, binaryCycleCornerLow, Matrix.submatrix,
        Matrix.transpose_apply, Fin.succAbove]
  have hlast : B.submatrix (6 : Fin 7).succAbove Fin.succ =
      binaryPathMatrix 6 (fun i => a i.succ.castSucc) x := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, binaryCycleMatrix, binaryPathMatrix, Matrix.submatrix, Fin.succAbove]
  change B.det = _
  rw [Matrix.det_succ_column_zero]
  norm_num [Fin.sum_univ_succ, hcol, hzero, hlast, Matrix.det_transpose,
    binaryCycleCornerLow_det, ← binaryPathDet_eq_det]
  all_goals ring
#print axioms Paper7EightCycle.binary_cycle_minor_seven_det

theorem binary_cycle_det_paths {R : Type*} [CommRing R] [CharP R 2]
    (a : Fin 8 → R) (x : R) :
    (binaryCycleMatrix a x).det =
      a 0 * binaryPathDet 7 (fun i => a i.succ) x +
        x^2 * (binaryPathDet 6 (fun i => a i.succ.succ) x +
          binaryPathDet 6 (fun i => a i.succ.castSucc) x) := by
  have hrow (j : Fin 8) : binaryCycleMatrix a x 0 j = ![a 0,x,0,0,0,0,0,x] j := rfl
  have hzero : (binaryCycleMatrix a x).submatrix Fin.succ Fin.succ =
      binaryPathMatrix 7 (fun i => a i.succ) x := by
    simpa only [Fin.succAbove_zero] using binary_cycle_minor_zero a x
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, hrow, hzero,
    binary_cycle_minor_one_det, binary_cycle_minor_seven_det, ← binaryPathDet_eq_det]
  all_goals ring_nf
  all_goals simp
#print axioms Paper7EightCycle.binary_cycle_det_paths

end Paper7EightCycle
