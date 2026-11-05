import Mathlib

/-! Sparse Laplace expansion in characteristic two. All dimensions in the
conversion lemmas remain symbolic; no determinant is enumerated. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open scoped BigOperators Matrix CharTwo

theorem binary_det_two_band_head {R : Type*} [CommRing R] [CharP R 2]
    (n : ℕ) (M : Matrix (Fin (n+2)) (Fin (n+2)) R)
    (hrow : ∀ j : Fin n, M 0 j.succ.succ = 0)
    (hcol : ∀ i : Fin n, M i.succ.succ 0 = 0) :
    M.det = M 0 0 * (M.submatrix Fin.succ Fin.succ).det +
      M 0 1 * M 1 0 *
        (M.submatrix (fun i : Fin n => i.succ.succ)
          (fun j : Fin n => j.succ.succ)).det := by
  have hminor : (M.submatrix Fin.succ (1 : Fin (n+2)).succAbove).det =
      M 1 0 * (M.submatrix (fun i : Fin n => i.succ.succ)
        (fun j : Fin n => j.succ.succ)).det := by
    rw [Matrix.det_succ_column_zero]
    simp only [Fin.sum_univ_succ]
    simp [Matrix.submatrix, hcol]
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ]
  simp [hrow, hminor, mul_assoc]
#print axioms Paper7EightCycle.binary_det_two_band_head

def binaryPathMatrix {R : Type*} [Zero R] (n : ℕ) (a : Fin n → R) (x : R) :
    Matrix (Fin n) (Fin n) R := fun i j =>
  if i = j then a i else if i.val+1 = j.val ∨ j.val+1 = i.val then x else 0
#print axioms Paper7EightCycle.binaryPathMatrix

def binaryPathDet {R : Type*} [CommRing R] (n : ℕ) (a : Fin n → R) (x : R) : R :=
  (binaryPathMatrix n a x).det
#print axioms Paper7EightCycle.binaryPathDet

theorem binaryPathDet_eq_det {R : Type*} [CommRing R]
    (n : ℕ) (a : Fin n → R) (x : R) :
    binaryPathDet n a x = (binaryPathMatrix n a x).det := rfl
#print axioms Paper7EightCycle.binaryPathDet_eq_det

theorem binaryPathDet_zero {R : Type*} [CommRing R] (a : Fin 0 → R) (x : R) :
    binaryPathDet 0 a x = 1 := by
  simp [binaryPathDet]
#print axioms Paper7EightCycle.binaryPathDet_zero

theorem binaryPathDet_one {R : Type*} [CommRing R] (a : Fin 1 → R) (x : R) :
    binaryPathDet 1 a x = a 0 := by
  simp [binaryPathDet, binaryPathMatrix]
#print axioms Paper7EightCycle.binaryPathDet_one

theorem binaryPathDet_recur {R : Type*} [CommRing R] [CharP R 2]
    (n : ℕ) (a : Fin (n+2) → R) (x : R) :
    binaryPathDet (n+2) a x =
      a 0 * binaryPathDet (n+1) (fun i => a i.succ) x +
        x^2 * binaryPathDet n (fun i => a i.succ.succ) x := by
  have hrow : ∀ j : Fin n, binaryPathMatrix (n+2) a x 0 j.succ.succ = 0 := by
    intro j
    simp [binaryPathMatrix, Fin.ext_iff]
  have hcol : ∀ i : Fin n, binaryPathMatrix (n+2) a x i.succ.succ 0 = 0 := by
    intro i
    simp [binaryPathMatrix, Fin.ext_iff]
  have htail : (binaryPathMatrix (n+2) a x).submatrix Fin.succ Fin.succ =
      binaryPathMatrix (n+1) (fun i => a i.succ) x := by
    funext i j
    simp [binaryPathMatrix, Matrix.submatrix, Fin.ext_iff]
  have htailtail : (binaryPathMatrix (n+2) a x).submatrix
      (fun i : Fin n => i.succ.succ) (fun j : Fin n => j.succ.succ) =
      binaryPathMatrix n (fun i => a i.succ.succ) x := by
    funext i j
    simp [binaryPathMatrix, Matrix.submatrix, Fin.ext_iff]
  rw [binaryPathDet_eq_det, binary_det_two_band_head n _ hrow hcol, htail, htailtail]
  rw [← binaryPathDet_eq_det, ← binaryPathDet_eq_det]
  simp [binaryPathMatrix, pow_two, mul_assoc]
#print axioms Paper7EightCycle.binaryPathDet_recur

end Paper7EightCycle
