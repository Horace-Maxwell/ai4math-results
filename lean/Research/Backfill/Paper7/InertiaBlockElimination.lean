import Research.Backfill.Paper7.InertiaQuadraticBridge

set_option autoImplicit false

noncomputable section

namespace Paper7Inertia

open Matrix Polynomial BackfillPaper7.Challenge
open scoped Matrix

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def upperShear (R : Matrix ι κ ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks 1 R 0 1
#print axioms Paper7Inertia.upperShear

theorem upperShear_inverse (R : Matrix ι κ ℝ) :
    upperShear R * upperShear (-R) = 1 ∧ upperShear (-R) * upperShear R = 1 := by
  constructor <;> simp [upperShear, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
#print axioms Paper7Inertia.upperShear_inverse

theorem upperShear_congruence (A : Matrix ι ι ℝ) (D : Matrix κ κ ℝ)
    (R : Matrix ι κ ℝ) :
    (upperShear R)ᵀ * Matrix.fromBlocks A 0 0 D * upperShear R =
      Matrix.fromBlocks A (A * R) (Rᵀ * A) (Rᵀ * A * R + D) := by
  simp [upperShear, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
#print axioms Paper7Inertia.upperShear_congruence

/-- Full positive and negative inertia of the block shear, including empty blocks. -/
theorem upperShear_inertia (A : Matrix ι ι ℝ) (D : Matrix κ κ ℝ)
    (R : Matrix ι κ ℝ) (hA : A.IsHermitian) (hD : D.IsHermitian) :
    nPos (Matrix.fromBlocks A (A * R) (Rᵀ * A) (Rᵀ * A * R + D)) =
        nPos A + nPos D ∧
      nNeg (Matrix.fromBlocks A (A * R) (Rᵀ * A) (Rᵀ * A * R + D)) =
        nNeg A + nNeg D := by
  have hM : (Matrix.fromBlocks A 0 0 D).IsHermitian :=
    hA.fromBlocks (by simp) hD
  have hi := inertia_congruence (Matrix.fromBlocks A 0 0 D)
    (upperShear R) (upperShear (-R)) hM
    (upperShear_inverse R).1 (upperShear_inverse R).2
  rw [upperShear_congruence] at hi
  have hb := inertia_block_diagonal A D
  exact ⟨hi.1.trans hb.1, hi.2.trans hb.2⟩
#print axioms Paper7Inertia.upperShear_inertia

def zeroPivotBlock (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, a; a, b]
#print axioms Paper7Inertia.zeroPivotBlock

theorem zeroPivotBlock_isHermitian (a b : ℝ) : (zeroPivotBlock a b).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [zeroPivotBlock]
#print axioms Paper7Inertia.zeroPivotBlock_isHermitian

def zeroPivotShear (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, -(b / (2*a)); 0, 1]
#print axioms Paper7Inertia.zeroPivotShear

theorem zeroPivotShear_inverse (a b : ℝ) :
    zeroPivotShear a b * zeroPivotShear a (-b) = 1 ∧
      zeroPivotShear a (-b) * zeroPivotShear a b = 1 := by
  constructor <;> apply Matrix.ext <;> intro i j <;>
    fin_cases i <;> fin_cases j <;>
    simp [zeroPivotShear, Matrix.mul_apply, Fin.sum_univ_succ, neg_div]
#print axioms Paper7Inertia.zeroPivotShear_inverse

theorem zeroPivotShear_elimination (a b : ℝ) (ha : a ≠ 0) :
    (zeroPivotShear a b)ᵀ * zeroPivotBlock a b * zeroPivotShear a b =
      zeroPivotBlock a 0 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [zeroPivotShear, zeroPivotBlock, Matrix.mul_apply, Fin.sum_univ_succ]
  field_simp [ha]
  ring
#print axioms Paper7Inertia.zeroPivotShear_elimination

def hyperbolicBasis : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1]
#print axioms Paper7Inertia.hyperbolicBasis

theorem hyperbolicBasis_inverse :
    hyperbolicBasis * ((1/2 : ℝ) • hyperbolicBasis) = 1 ∧
      ((1/2 : ℝ) • hyperbolicBasis) * hyperbolicBasis = 1 := by
  constructor <;> apply Matrix.ext <;> intro i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [hyperbolicBasis, Matrix.mul_apply, Fin.sum_univ_succ]
#print axioms Paper7Inertia.hyperbolicBasis_inverse

theorem hyperbolicBasis_diagonal (a : ℝ) :
    hyperbolicBasisᵀ * zeroPivotBlock a 0 * hyperbolicBasis =
      Matrix.diagonal ![2*a, -(2*a)] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hyperbolicBasis, zeroPivotBlock, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.diagonal] <;> ring
#print axioms Paper7Inertia.hyperbolicBasis_diagonal

theorem inertia_diagonal_two (r s : ℝ) :
    nPos (Matrix.diagonal ![r, s]) = (if 0 < r then 1 else 0) + (if 0 < s then 1 else 0) ∧
      nNeg (Matrix.diagonal ![r, s]) = (if r < 0 then 1 else 0) + (if s < 0 then 1 else 0) := by
  have hc : (Matrix.diagonal ![r, s]).charpoly = (X - C r) * (X - C s) := by
    simp [Matrix.charpoly_diagonal, Fin.prod_univ_succ]
  have he : eigs (Matrix.diagonal ![r, s]) = {r} + {s} := by
    rw [eigs, hc, Polynomial.roots_mul
      (mul_ne_zero (Polynomial.X_sub_C_ne_zero r) (Polynomial.X_sub_C_ne_zero s)),
      Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
  constructor
  · simp only [nPos, he, Multiset.filter_add, Multiset.filter_singleton]
    split_ifs <;> simp
  · simp only [nNeg, he, Multiset.filter_add, Multiset.filter_singleton]
    split_ifs <;> simp

#print axioms Paper7Inertia.inertia_diagonal_two

/-- The zero-pivot block always contributes one positive and one negative root,
regardless of its second diagonal entry and of the sign of its nonzero edge. -/
theorem zeroPivotBlock_inertia (a b : ℝ) (ha : a ≠ 0) :
    nPos (zeroPivotBlock a b) = 1 ∧ nNeg (zeroPivotBlock a b) = 1 := by
  have hs := inertia_congruence (zeroPivotBlock a b)
    (zeroPivotShear a b) (zeroPivotShear a (-b))
    (zeroPivotBlock_isHermitian a b)
    (zeroPivotShear_inverse a b).1 (zeroPivotShear_inverse a b).2
  rw [zeroPivotShear_elimination a b ha] at hs
  have hh := inertia_congruence (zeroPivotBlock a 0)
    hyperbolicBasis ((1/2 : ℝ) • hyperbolicBasis)
    (zeroPivotBlock_isHermitian a 0)
    hyperbolicBasis_inverse.1 hyperbolicBasis_inverse.2
  rw [hyperbolicBasis_diagonal] at hh
  have hd := inertia_diagonal_two (2*a) (-(2*a))
  have hD : nPos (Matrix.diagonal ![2*a, -(2*a)]) = 1 ∧
      nNeg (Matrix.diagonal ![2*a, -(2*a)]) = 1 := by
    rcases lt_or_gt_of_ne ha with hn | hp
    · have hn' : 2*a < 0 := by linarith
      have hp' : 0 < -(2*a) := by linarith
      simpa [hn', hp', not_lt_of_ge hn'.le, not_lt_of_ge hp'.le] using hd
    · have hp' : 0 < 2*a := by linarith
      have hn' : -(2*a) < 0 := by linarith
      simpa [hn', hp', not_lt_of_ge hn'.le, not_lt_of_ge hp'.le] using hd
  exact ⟨hs.1.symm.trans (hh.1.symm.trans hD.1),
    hs.2.symm.trans (hh.2.symm.trans hD.2)⟩
#print axioms Paper7Inertia.zeroPivotBlock_inertia

end Paper7Inertia
