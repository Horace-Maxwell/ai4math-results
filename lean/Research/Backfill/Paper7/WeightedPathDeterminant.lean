import Research.Backfill.Paper7.WeightedContinuant

set_option autoImplicit false
noncomputable section
namespace Paper7Schwenk
open Finset
open scoped Classical

def weightedPath {K : Type*} [CommRing K] {n : ℕ} (d l : Fin n → K) :
    Matrix (Fin n) (Fin n) K := fun i j =>
  if i = j then d i else
    if i.val+1 = j.val ∨ j.val+1 = i.val then -l i else 0
#print axioms Paper7Schwenk.weightedPath

theorem weightedPath_tail {K : Type*} [CommRing K] (n : ℕ)
    (d l : Fin (n+1) → K) :
    (weightedPath d l).submatrix Fin.succ Fin.succ =
      weightedPath (d ∘ Fin.succ) (l ∘ Fin.succ) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.submatrix_apply, weightedPath, Function.comp_apply,
    Fin.succ_inj, Fin.val_succ, Nat.add_right_cancel_iff]
#print axioms Paper7Schwenk.weightedPath_tail

theorem weightedPath_far_zero {K : Type*} [CommRing K] (n : ℕ)
    (d l : Fin (n+2) → K) (j : Fin n) :
    weightedPath d l 0 j.succ.succ = 0 ∧ weightedPath d l j.succ.succ 0 = 0 := by
  have hj : (j.succ.succ : Fin (n+2)) ≠ 0 := Fin.succ_ne_zero _
  have hh : ¬(0+1 = j.val+1+1 ∨ j.val+1+1+1 = 0) := by omega
  have hh' : ¬(j.val+1+1+1 = 0 ∨ 0+1 = j.val+1+1) := by omega
  constructor
  · change (if (0 : Fin (n+2)) = j.succ.succ then d 0 else
      if 0+1 = j.val+1+1 ∨ j.val+1+1+1 = 0 then -l 0 else 0) = 0
    rw [ite_eq_right (Ne.symm hj)]
    exact ite_eq_right hh
  · change (if j.succ.succ = (0 : Fin (n+2)) then d j.succ.succ else
      if j.val+1+1+1 = 0 ∨ 0+1 = j.val+1+1 then -l j.succ.succ else 0) = 0
    rw [ite_eq_right hj]
    exact ite_eq_right hh'
#print axioms Paper7Schwenk.weightedPath_far_zero

/-- The off-diagonal cofactor is triangular in its first column. -/
theorem weightedPath_cross_minor {K : Type*} [CommRing K] (n : ℕ)
    (d l : Fin (n+2) → K) :
    ((weightedPath d l).submatrix Fin.succ (Fin.succ (0 : Fin (n+1))).succAbove).det =
      -l (Fin.succ 0) *
        (weightedPath (fun i : Fin n => d i.succ.succ)
          (fun i : Fin n => l i.succ.succ)).det := by
  let M := (weightedPath d l).submatrix Fin.succ (Fin.succ (0 : Fin (n+1))).succAbove
  have hcol0 : M 0 0 = -l (Fin.succ 0) := by
    simp [M, Matrix.submatrix_apply, weightedPath]
  have hcol (i : Fin n) : M i.succ 0 = 0 := by
    simpa only [M, Matrix.submatrix_apply, Fin.succAbove_succ_self,
      Fin.castSucc_zero] using (weightedPath_far_zero n d l i).2
  have hminor : M.submatrix Fin.succ Fin.succ =
      weightedPath (fun i : Fin n => d i.succ.succ)
        (fun i : Fin n => l i.succ.succ) := by
    have hskip (j : Fin n) :
        (Fin.succ (0 : Fin (n+1))).succAbove j.succ = j.succ.succ :=
      Fin.succAbove_succ_of_lt _ _ (Fin.succ_pos j)
    apply Matrix.ext
    intro i j
    simp only [M, Matrix.submatrix_apply, hskip, weightedPath, Fin.succ_inj,
      Fin.val_succ, Nat.add_right_cancel_iff]
  change M.det = _
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, hcol0, Fin.succAbove_zero, hminor,
    hcol, mul_zero, zero_mul, sum_const_zero, add_zero]
#print axioms Paper7Schwenk.weightedPath_cross_minor

theorem weightedPath_det_recurrence {K : Type*} [CommRing K] (n : ℕ)
    (d l : Fin (n+2) → K) :
    (weightedPath d l).det =
      d 0 * (weightedPath (d ∘ Fin.succ) (l ∘ Fin.succ)).det -
        l 0 * l (Fin.succ 0) *
          (weightedPath (fun i : Fin n => d i.succ.succ)
            (fun i : Fin n => l i.succ.succ)).det := by
  have h00 : weightedPath d l 0 0 = d 0 := by simp [weightedPath]
  have h01 : weightedPath d l 0 (Fin.succ 0) = -l 0 := by simp [weightedPath]
  have hz (c : Fin n → K) : ∑ j : Fin n, c j *
      weightedPath d l 0 j.succ.succ *
      ((weightedPath d l).submatrix Fin.succ j.succ.succ.succAbove).det = 0 := by
    apply Finset.sum_eq_zero
    intro j _hj
    rw [(weightedPath_far_zero n d l j).1, mul_zero, zero_mul]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  rw [hz]
  simp only [Fin.val_zero, pow_zero, one_mul, h00, h01, Fin.succAbove_zero,
    weightedPath_tail, Fin.val_succ, zero_add, pow_one,
    weightedPath_cross_minor]
  ring
#print axioms Paper7Schwenk.weightedPath_det_recurrence

/-- Exact determinant/continuant bridge in every dimension, including 0 and 1. -/
theorem weightedPath_det_continuant {K : Type*} [CommRing K] (n : ℕ)
    (d l : Fin n → K) :
    (weightedPath d l).det = continuant (List.ofFn (fun i => (d i,l i))) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Matrix.det_fin_zero, List.ofFn_zero, continuant]
  | one => simp [weightedPath, List.ofFn_succ, continuant]
  | more n ih0 ih1 =>
    rw [weightedPath_det_recurrence, ih1, ih0]
    simp only [List.ofFn_succ, continuant, Function.comp_apply]
#print axioms Paper7Schwenk.weightedPath_det_continuant

end Paper7Schwenk
