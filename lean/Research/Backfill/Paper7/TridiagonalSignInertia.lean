import Research.Backfill.Paper7.MatrixInertiaEmbeddings
import Research.Backfill.Paper7.TridiagonalComparison

set_option autoImplicit false

noncomputable section

namespace Paper7Comparison

open Matrix BackfillPaper7.Challenge Paper7Inertia
open scoped Matrix

theorem alternating_sign_square (n : ℕ) : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
  rw [← mul_pow]
  norm_num
#print axioms Paper7Comparison.alternating_sign_square

theorem alternating_sign_neighbors (n k : ℕ) (h : n + 1 = k ∨ k + 1 = n) :
    (-1 : ℝ) ^ n * (-1 : ℝ) ^ k = -1 := by
  rcases h with h | h
  · subst k
    rw [pow_succ, ← mul_assoc, alternating_sign_square]
    norm_num
  · subst n
    rw [mul_comm, pow_succ, ← mul_assoc, alternating_sign_square]
    norm_num
#print axioms Paper7Comparison.alternating_sign_neighbors

def alternatingDiagonal {b : ℕ} (Y : Finset (Fin b)) : Matrix Y Y ℝ :=
  Matrix.diagonal (fun i : Y => (-1 : ℝ) ^ i.val.val)
#print axioms Paper7Comparison.alternatingDiagonal

theorem alternatingDiagonal_inverse {b : ℕ} (Y : Finset (Fin b)) :
    alternatingDiagonal Y * alternatingDiagonal Y = 1 := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [alternatingDiagonal, Matrix.mul_apply, Matrix.diagonal_apply,
      alternating_sign_square]
  · simp [alternatingDiagonal, Matrix.mul_apply, Matrix.diagonal_apply, hij]
#print axioms Paper7Comparison.alternatingDiagonal_inverse

/-- A local sign change on a path-indexed matrix; arbitrary odd cycles are not asserted bipartite. -/
theorem alternating_tridiag_congruence {b : ℕ} (Y : Finset (Fin b)) (t : Fin b → ℝ) :
    (alternatingDiagonal Y)ᵀ * tridiag Y (fun k => -t k) * alternatingDiagonal Y =
      -(tridiag Y t) := by
  apply Matrix.ext
  intro i j
  have hentry : ((alternatingDiagonal Y)ᵀ *
      tridiag Y (fun k => -t k) * alternatingDiagonal Y) i j =
      ((-1 : ℝ) ^ i.val.val * (-1 : ℝ) ^ j.val.val) *
        tridiag Y (fun k => -t k) i j := by
    simp [alternatingDiagonal, Matrix.diagonal_transpose, Matrix.mul_apply,
      Matrix.diagonal_apply, mul_assoc, mul_left_comm, mul_comm]
  rw [hentry]
  by_cases hij : i = j
  · subst j
    simp [tridiag, alternating_sign_square]
  · by_cases ha : i.val.val + 1 = j.val.val ∨ j.val.val + 1 = i.val.val
    · rw [alternating_sign_neighbors _ _ ha]
      simp [tridiag, hij, ha]
    · simp [tridiag, hij, ha]
#print axioms Paper7Comparison.alternating_tridiag_congruence

theorem tridiag_neg_diagonal_inertia {b : ℕ} (Y : Finset (Fin b)) (t : Fin b → ℝ) :
    nPos (tridiag Y (fun k => -t k)) = nNeg (tridiag Y t) ∧
      nNeg (tridiag Y (fun k => -t k)) = nPos (tridiag Y t) ∧
      nZero (tridiag Y (fun k => -t k)) = nZero (tridiag Y t) := by
  have h := inertia_congruence (tridiag Y (fun k => -t k))
    (alternatingDiagonal Y) (alternatingDiagonal Y)
    (tridiag_isHermitian Y (fun k => -t k))
    (alternatingDiagonal_inverse Y) (alternatingDiagonal_inverse Y)
  rw [alternating_tridiag_congruence] at h
  rw [nPos_neg _ (tridiag_isHermitian Y t), nNeg_neg _ (tridiag_isHermitian Y t)] at h
  have ht := inertia_total (tridiag Y t) (tridiag_isHermitian Y t)
  have hn := inertia_total (tridiag Y (fun k => -t k))
    (tridiag_isHermitian Y (fun k => -t k))
  refine ⟨h.1.symm, h.2.symm, ?_⟩
  omega
#print axioms Paper7Comparison.tridiag_neg_diagonal_inertia

theorem fk_neg (b : ℕ) (p q : Fin b → ℕ) (m : ℝ) (k : Fin b) :
    fk b p q (-m) k = -(fk b p q m k) := by
  simp only [fk, neg_sq, div_neg, mul_neg, neg_div, neg_add_rev]
  ring
#print axioms Paper7Comparison.fk_neg

/-- The compressed matrices at m and -m have opposite inertia, with zero roots retained. -/
theorem reduced_tridiag_negative_parameter (b : ℕ) (p q : Fin b → ℕ)
    (Y : Finset (Fin b)) (m : ℝ) :
    nNeg (tridiag Y (fun k => fk b p q (-m) k - (-m))) =
        nPos (tridiag Y (fun k => fk b p q m k - m)) ∧
      nZero (tridiag Y (fun k => fk b p q (-m) k - (-m))) =
        nZero (tridiag Y (fun k => fk b p q m k - m)) := by
  have hd : (fun k => fk b p q (-m) k - (-m)) =
      (fun k => -(fk b p q m k - m)) := by
    funext k
    rw [fk_neg]
    ring
  rw [hd]
  exact (tridiag_neg_diagonal_inertia Y (fun k => fk b p q m k - m)).2
#print axioms Paper7Comparison.reduced_tridiag_negative_parameter

end Paper7Comparison
