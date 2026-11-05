import Research.Backfill.Paper7.BorderedPivotInertia
import Research.Backfill.Paper7.PivotRecurrence

set_option autoImplicit false

noncomputable section

namespace Paper7Pivots

open Matrix BackfillPaper7.Challenge Paper7Inertia
open scoped Matrix

theorem inertia_submatrix_equiv {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (M : Matrix ι ι ℝ) (e : κ ≃ ι) :
    nPos (M.submatrix e e) = nPos M ∧ nNeg (M.submatrix e e) = nNeg M := by
  have hc : (M.submatrix e e).charpoly = M.charpoly :=
    Matrix.charpoly_reindex e.symm M
  constructor <;> simp only [nPos, nNeg, eigs, hc]
#print axioms Paper7Pivots.inertia_submatrix_equiv

def firstCoupling (N : ℕ) (c : ℝ) : Fin N → ℝ := fun i => if i.val = 0 then c else 0
#print axioms Paper7Pivots.firstCoupling

/-- Reindex the original matrix by its actual first vertex and tail. -/
theorem tridiag_split_one (N : ℕ) (t a : ℕ → ℝ) :
    (tridiagGen (1+N) t a).submatrix
      (finSumFinEquiv : Fin 1 ⊕ Fin N ≃ Fin (1+N)) finSumFinEquiv =
      Matrix.fromBlocks (singletonBlock (t 0))
        (fun _ j => firstCoupling N (a 0) j) (fun i _ => firstCoupling N (a 0) i)
        (tridiagGen N (fun k => t (k+1)) (fun k => a (k+1))) := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i
    fin_cases j
    simp [tridiagGen, Matrix.submatrix, Matrix.fromBlocks, singletonBlock]
  · fin_cases i
    simp [tridiagGen, Matrix.submatrix, Matrix.fromBlocks, firstCoupling,
      Nat.add_comm]
  · fin_cases j
    simp [tridiagGen, Matrix.submatrix, Matrix.fromBlocks, firstCoupling,
      Nat.add_comm]
  · simp [tridiagGen, Matrix.submatrix, Matrix.fromBlocks, Fin.ext_iff,
      Nat.add_comm, Nat.add_left_comm]
#print axioms Paper7Pivots.tridiag_split_one

theorem tridiag_single_schur (N : ℕ) (t a : ℕ → ℝ) (d : ℝ) :
    singlePivotSchur d (firstCoupling N (a 0))
      (tridiagGen N (fun k => t (k+1)) (fun k => a (k+1))) =
        tridiagGen N (schurDiagonal t a d) (fun k => a (k+1)) := by
  apply Matrix.ext
  intro i j
  by_cases he : i = j
  · subst j
    by_cases hi : i.val = 0 <;>
      simp [singlePivotSchur, firstCoupling, tridiagGen, schurDiagonal, hi, pow_two]
  · by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0 <;>
      simp_all [singlePivotSchur, firstCoupling, tridiagGen, Fin.ext_iff]
#print axioms Paper7Pivots.tridiag_single_schur

/-- Ordinary elimination changes only the first diagonal entry of the original tail. -/
theorem tridiag_nonzero_step (N : ℕ) (t a : ℕ → ℝ) (ht : t 0 ≠ 0) :
    nPos (tridiagGen (N+1) t a) = (if 0 < t 0 then 1 else 0) +
        nPos (tridiagGen N (schurDiagonal t a (t 0)) (fun k => a (k+1))) ∧
      nNeg (tridiagGen (N+1) t a) = (if t 0 < 0 then 1 else 0) +
        nNeg (tridiagGen N (schurDiagonal t a (t 0)) (fun k => a (k+1))) := by
  have he := inertia_submatrix_equiv (tridiagGen (1+N) t a)
    (finSumFinEquiv : Fin 1 ⊕ Fin N ≃ Fin (1+N))
  rw [tridiag_split_one] at he
  have hs := singlePivot_inertia (t 0) (firstCoupling N (a 0))
    (tridiagGen N (fun k => t (k+1)) (fun k => a (k+1))) ht
    (tridiagGen_isHermitian N _ _)
  rw [tridiag_single_schur] at hs
  have hp := congrArg (fun n => nPos (tridiagGen n t a)) (Nat.add_comm N 1)
  have hn := congrArg (fun n => nNeg (tridiagGen n t a)) (Nat.add_comm N 1)
  exact ⟨hp.trans (he.1.symm.trans hs.1), hn.trans (he.2.symm.trans hs.2)⟩
#print axioms Paper7Pivots.tridiag_nonzero_step

/-- The real first two vertices form the zero pivot block; only the second can
couple to the remaining original path. -/
theorem tridiag_split_two_zero (N : ℕ) (t a : ℕ → ℝ) (ht : t 0 = 0) :
    (tridiagGen (2+N) t a).submatrix
      (finSumFinEquiv : Fin 2 ⊕ Fin N ≃ Fin (2+N)) finSumFinEquiv =
      Matrix.fromBlocks (zeroPivotBlock (a 0) (t 1))
        (zeroPairCoupling (firstCoupling N (a 1)))
        (zeroPairCoupling (firstCoupling N (a 1)))ᵀ
        (tridiagGen N (fun k => t (k+2)) (fun k => a (k+2))) := by
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;>
      simp [tridiagGen, Matrix.submatrix, Matrix.fromBlocks, zeroPivotBlock, ht]
  · fin_cases i <;>
      simp [tridiagGen, Matrix.submatrix, Matrix.fromBlocks, zeroPairCoupling,
        firstCoupling, Nat.add_comm]
  · fin_cases j <;>
      simp [tridiagGen, Matrix.submatrix, Matrix.fromBlocks, zeroPairCoupling,
        firstCoupling, Nat.add_comm]
  · simp [tridiagGen, Matrix.submatrix, Matrix.fromBlocks, Fin.ext_iff,
      Nat.add_comm, Nat.add_left_comm]
#print axioms Paper7Pivots.tridiag_split_two_zero

/-- Actual two-index elimination with an unchanged tail, for either sign count. -/
theorem tridiag_zero_step (N : ℕ) (t a : ℕ → ℝ) (ht : t 0 = 0) (ha : a 0 ≠ 0) :
    nPos (tridiagGen (N+2) t a) =
        1 + nPos (tridiagGen N (fun k => t (k+2)) (fun k => a (k+2))) ∧
      nNeg (tridiagGen (N+2) t a) =
        1 + nNeg (tridiagGen N (fun k => t (k+2)) (fun k => a (k+2))) := by
  have he := inertia_submatrix_equiv (tridiagGen (2+N) t a)
    (finSumFinEquiv : Fin 2 ⊕ Fin N ≃ Fin (2+N))
  rw [tridiag_split_two_zero N t a ht] at he
  have hs := zeroPair_inertia (a 0) (t 1) (firstCoupling N (a 1))
    (tridiagGen N (fun k => t (k+2)) (fun k => a (k+2))) ha
    (tridiagGen_isHermitian N _ _)
  have hp := congrArg (fun n => nPos (tridiagGen n t a)) (Nat.add_comm N 2)
  have hn := congrArg (fun n => nNeg (tridiagGen n t a)) (Nat.add_comm N 2)
  exact ⟨hp.trans (he.1.symm.trans hs.1), hn.trans (he.2.symm.trans hs.2)⟩
#print axioms Paper7Pivots.tridiag_zero_step

end Paper7Pivots
