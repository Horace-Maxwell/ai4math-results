import Research.Backfill.Paper7.InertiaBlockElimination

/-! Generic Schur inertia for an invertible lower-right Hermitian block.
Author: /root/paper6_tree_actual_final_review/p6_binding_spotcheck.
This NEW source is an uncompiled candidate; it is not an acceptance receipt. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix

namespace Paper7Lemma21

open BackfillPaper7.Challenge

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def lowerShear (R : Matrix κ ι ℝ) : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks 1 0 R 1
#print axioms Paper7Lemma21.lowerShear

theorem lowerShear_inverse (R : Matrix κ ι ℝ) :
    lowerShear R * lowerShear (-R) = 1 ∧
      lowerShear (-R) * lowerShear R = 1 := by
  constructor <;>
    simp [lowerShear, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
#print axioms Paper7Lemma21.lowerShear_inverse

/-- Actual block congruence, without requiring the Schur complement invertible. -/
theorem lowerShear_schur_congruence (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (D : Matrix κ κ ℝ) (hD : D.IsHermitian) [Invertible D] :
    (lowerShear (-(D⁻¹ * Bᵀ)))ᵀ * Matrix.fromBlocks A B Bᵀ D *
        lowerShear (-(D⁻¹ * Bᵀ)) =
      Matrix.fromBlocks (A - B * D⁻¹ * Bᵀ) 0 0 D := by
  let R : Matrix κ ι ℝ := -(D⁻¹ * Bᵀ)
  change (lowerShear R)ᵀ * Matrix.fromBlocks A B Bᵀ D * lowerShear R = _
  have hDt : (D⁻¹)ᵀ = D⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hD.inv.eq
  have hRt : Rᵀ = -(B * D⁻¹) := by
    simp only [R, Matrix.transpose_neg, Matrix.transpose_mul,
      Matrix.transpose_transpose, hDt]
  have hBR : B + Rᵀ * D = 0 := by
    rw [hRt, Matrix.neg_mul, Matrix.inv_mul_cancel_right_of_invertible,
      add_neg_cancel]
  have hDR : Bᵀ + D * R = 0 := by
    simp only [R, Matrix.mul_neg, Matrix.mul_inv_cancel_left_of_invertible,
      add_neg_cancel]
  simp only [lowerShear, Matrix.fromBlocks_transpose, Matrix.transpose_one,
    Matrix.transpose_zero, Matrix.fromBlocks_multiply, Matrix.one_mul,
    Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, hBR, hDR]
  rw [hRt, Matrix.neg_mul, ← sub_eq_add_neg]
#print axioms Paper7Lemma21.lowerShear_schur_congruence

/-- Both inertia counts split exactly, including singular or empty Schur blocks. -/
theorem schur_inertia (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (D : Matrix κ κ ℝ) (hA : A.IsHermitian) (hD : D.IsHermitian) [Invertible D] :
    nPos (Matrix.fromBlocks A B Bᵀ D) = nPos (A - B * D⁻¹ * Bᵀ) + nPos D ∧
      nNeg (Matrix.fromBlocks A B Bᵀ D) = nNeg (A - B * D⁻¹ * Bᵀ) + nNeg D := by
  let R : Matrix κ ι ℝ := -(D⁻¹ * Bᵀ)
  have hM : (Matrix.fromBlocks A B Bᵀ D).IsHermitian :=
    hA.fromBlocks (by simp only [Matrix.conjTranspose_eq_transpose_of_trivial]) hD
  have hinv := lowerShear_inverse R
  have hi := Paper7Inertia.inertia_congruence (Matrix.fromBlocks A B Bᵀ D)
    (lowerShear R) (lowerShear (-R)) hM hinv.1 hinv.2
  rw [lowerShear_schur_congruence A B D hD] at hi
  have hblock := Paper7Inertia.inertia_block_diagonal (A - B * D⁻¹ * Bᵀ) D
  exact ⟨hi.1.symm.trans hblock.1, hi.2.symm.trans hblock.2⟩
#print axioms Paper7Lemma21.schur_inertia

end Paper7Lemma21
