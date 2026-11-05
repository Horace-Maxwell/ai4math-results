import Research.Backfill.Paper7.InertiaBlockElimination

set_option autoImplicit false

noncomputable section

namespace Paper7Inertia

open Matrix Polynomial BackfillPaper7.Challenge
open scoped Matrix

variable {κ : Type} [Fintype κ] [DecidableEq κ]

def singletonBlock (d : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of (fun _ _ => d)
#print axioms Paper7Inertia.singletonBlock

theorem singletonBlock_inertia (d : ℝ) :
    nPos (singletonBlock d) = (if 0 < d then 1 else 0) ∧
      nNeg (singletonBlock d) = (if d < 0 then 1 else 0) := by
  have hc : (singletonBlock d).charpoly = X - C d := by
    rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]
    rfl
  constructor
  · simp only [nPos, eigs, hc, Polynomial.roots_X_sub_C, Multiset.filter_singleton]
    split_ifs <;> simp
  · simp only [nNeg, eigs, hc, Polynomial.roots_X_sub_C, Multiset.filter_singleton]
    split_ifs <;> simp
#print axioms Paper7Inertia.singletonBlock_inertia

def singlePivotSchur (d : ℝ) (v : κ → ℝ) (D : Matrix κ κ ℝ) : Matrix κ κ ℝ :=
  D - Matrix.of (fun i j => v i * v j / d)
#print axioms Paper7Inertia.singlePivotSchur

/-- Ordinary Schur elimination for every tail dimension, including the empty tail.
The sign of d is unrestricted, but this lemma alone is not the frozen Lemma52. -/
theorem singlePivot_inertia (d : ℝ) (v : κ → ℝ) (D : Matrix κ κ ℝ)
    (hd : d ≠ 0) (hD : D.IsHermitian) :
    nPos (Matrix.fromBlocks (singletonBlock d) (Matrix.of (fun _ j => v j))
      (Matrix.of (fun i _ => v i)) D) =
        (if 0 < d then 1 else 0) + nPos (singlePivotSchur d v D) ∧
      nNeg (Matrix.fromBlocks (singletonBlock d) (Matrix.of (fun _ j => v j))
      (Matrix.of (fun i _ => v i)) D) =
        (if d < 0 then 1 else 0) + nNeg (singlePivotSchur d v D) := by
  let R : Matrix (Fin 1) κ ℝ := Matrix.of (fun _ j => v j / d)
  have hA : (singletonBlock d).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [singletonBlock]
  have hS : (singlePivotSchur d v D).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    have h := hD.apply i j
    simp only [star_trivial] at h
    simp only [singlePivotSchur, Matrix.sub_apply, Matrix.of_apply, star_trivial]
    rw [h]
    ring
  have hAR : singletonBlock d * R = Matrix.of (fun (_ : Fin 1) j => v j) := by
    apply Matrix.ext
    intro i j
    simp [singletonBlock, R, Matrix.mul_apply]
    field_simp [hd]
  have hRA : Rᵀ * singletonBlock d = Matrix.of (fun i (_ : Fin 1) => v i) := by
    apply Matrix.ext
    intro i j
    simp [singletonBlock, R, Matrix.mul_apply]
    field_simp [hd]
  have hRAR : Rᵀ * singletonBlock d * R = Matrix.of (fun i j => v i * v j / d) := by
    rw [hRA]
    apply Matrix.ext
    intro i j
    simp [R, Matrix.mul_apply]
    ring
  have htail : Matrix.of (fun i j => v i * v j / d) + singlePivotSchur d v D = D := by
    unfold singlePivotSchur
    abel
  have hi := upperShear_inertia (singletonBlock d) (singlePivotSchur d v D) R hA hS
  rw [hRAR, hAR, hRA, htail, (singletonBlock_inertia d).1,
    (singletonBlock_inertia d).2] at hi
  exact hi
#print axioms Paper7Inertia.singlePivot_inertia

def zeroPairCoupling (v : κ → ℝ) : Matrix (Fin 2) κ ℝ :=
  Matrix.of (fun i j => if i = 0 then 0 else v j)
#print axioms Paper7Inertia.zeroPairCoupling

/-- The crucial zero-pivot step for arbitrary tails. Coupling through the second
vertex gives a zero Schur correction, so the original tail is unchanged. -/
theorem zeroPair_inertia (a b : ℝ) (v : κ → ℝ) (D : Matrix κ κ ℝ)
    (ha : a ≠ 0) (hD : D.IsHermitian) :
    nPos (Matrix.fromBlocks (zeroPivotBlock a b) (zeroPairCoupling v)
      (zeroPairCoupling v)ᵀ D) = 1 + nPos D ∧
      nNeg (Matrix.fromBlocks (zeroPivotBlock a b) (zeroPairCoupling v)
        (zeroPairCoupling v)ᵀ D) = 1 + nNeg D := by
  let R : Matrix (Fin 2) κ ℝ := Matrix.of (fun i j => if i = 0 then v j / a else 0)
  have hA := zeroPivotBlock_isHermitian a b
  have hAR : zeroPivotBlock a b * R = zeroPairCoupling v := by
    apply Matrix.ext
    intro i j
    fin_cases i <;>
      norm_num [R, zeroPivotBlock, zeroPairCoupling, Matrix.mul_apply,
        Fin.sum_univ_succ]
    field_simp [ha]
  have hRA : Rᵀ * zeroPivotBlock a b = (zeroPairCoupling v)ᵀ := by
    rw [← hAR, Matrix.transpose_mul, hA.isSymm]
  have hRAR : Rᵀ * zeroPivotBlock a b * R = 0 := by
    rw [hRA]
    apply Matrix.ext
    intro i j
    simp [R, zeroPairCoupling, Matrix.mul_apply]
  have hi := upperShear_inertia (zeroPivotBlock a b) D R hA hD
  rw [hRAR, hAR, hRA, zero_add, (zeroPivotBlock_inertia a b ha).1,
    (zeroPivotBlock_inertia a b ha).2] at hi
  exact hi
#print axioms Paper7Inertia.zeroPair_inertia

end Paper7Inertia
