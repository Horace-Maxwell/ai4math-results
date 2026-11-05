import Research.Backfill.Paper7.PruningCoordinateMono
import Research.Backfill.Paper7.MatrixInertiaEmbeddings

/-! Exact positive/nonnegative inertia under diagonal increases and the
dimension-correct principal-submatrix upper bound. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace Paper7Pruning
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7Inertia Paper7Comparison

theorem diagonal_add_inertia_mono {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    nPos A ≤ nPos (A + Matrix.diagonal w) ∧
      nPos A + nZero A ≤ nPos (A + Matrix.diagonal w) + nZero (A + Matrix.diagonal w) := by
  have hq (v : ι → ℝ) : A.toQuadraticForm' v ≤ (A + Matrix.diagonal w).toQuadraticForm' v := by
    rw [quadratic_add_apply, quadratic_diagonal]
    have hnonneg : 0 ≤ (QuadraticMap.weightedSumSquares ℝ w) v := by
      rw [QuadraticMap.weightedSumSquares_apply]
      apply Finset.sum_nonneg
      intro i _
      change 0 ≤ w i * (v i * v i)
      exact mul_nonneg (hw i) (mul_self_nonneg _)
    linarith
  have hB := hA.add (Matrix.isHermitian_diagonal w)
  exact ⟨(inertia_mono A _ hA hB hq).1, nonneg_inertia_mono A _ hA hB hq⟩
#print axioms Paper7Pruning.diagonal_add_inertia_mono

theorem principal_positive_upper {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (M : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (f : κ → ι) (hf : Function.Injective f) :
    nPos M + Fintype.card κ ≤ nPos (M.submatrix f f) + Fintype.card ι := by
  have hn := (principal_negative_inertia_bounds M hM f hf).2
  have htotal := inertia_total M hM
  have hsub := inertia_total (M.submatrix f f) (hM.submatrix f)
  omega
#print axioms Paper7Pruning.principal_positive_upper

theorem fk_coordinate_mono (b : ℕ) (p q p' q' : Fin b → ℕ) (m : ℝ)
    (hm : 2 ≤ m) (hp : ∀ i, p i ≤ p' i) (hq : ∀ i, q i ≤ q' i) (i : Fin b) :
    fk b p q m i ≤ fk b p' q' m i := by
  have hm0 : 0 ≤ m := by linarith
  have hd : 0 ≤ m^2-1 := by nlinarith
  have hpR : (p i : ℝ) ≤ p' i := by exact_mod_cast hp i
  have hqR : (q i : ℝ) ≤ q' i := by exact_mod_cast hq i
  unfold fk
  exact add_le_add (div_le_div_of_nonneg_right hpR hm0)
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hqR hm0) hd)
#print axioms Paper7Pruning.fk_coordinate_mono

theorem pathMatrix_isHermitian (b d : ℕ) (x : PQ b) (m : ℝ) :
    (pathMatrix b d x m).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp [pathMatrix]
  · simp [pathMatrix, h, Ne.symm h, or_comm]
#print axioms Paper7Pruning.pathMatrix_isHermitian

theorem pathMatrix_diagonal_difference (b d : ℕ) (x y : PQ b) (m : ℝ) :
    pathMatrix b d y m = pathMatrix b d x m +
      Matrix.diagonal (fun i : PathIndex b =>
        fk b («prefix» d y).1 («prefix» d y).2 m i.val -
          fk b («prefix» d x).1 («prefix» d x).2 m i.val) := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp only [pathMatrix, ite_true, Matrix.add_apply, Matrix.diagonal_apply_eq]
    ring
  · simp [pathMatrix, Matrix.add_apply, h]
#print axioms Paper7Pruning.pathMatrix_diagonal_difference

theorem pathMatrix_inertia_mono (b d : ℕ) (x y : PQ b)
    (hxy : ∀ i, x.1 i ≤ y.1 i ∧ x.2 i ≤ y.2 i) (m : ℝ) (hm : 2 ≤ m) :
    nPos (pathMatrix b d x m) ≤ nPos (pathMatrix b d y m) ∧
      nPos (pathMatrix b d x m) + nZero (pathMatrix b d x m) ≤
        nPos (pathMatrix b d y m) + nZero (pathMatrix b d y m) := by
  have hp := prefix_coordinate_mono b d x y hxy
  have h := diagonal_add_inertia_mono (pathMatrix b d x m) (pathMatrix_isHermitian b d x m)
    (fun i : PathIndex b => fk b («prefix» d y).1 («prefix» d y).2 m i.val -
      fk b («prefix» d x).1 («prefix» d x).2 m i.val)
    (fun i => sub_nonneg.mpr (fk_coordinate_mono b _ _ _ _ m hm
      (fun k => (hp k).1) (fun k => (hp k).2) i.val))
  rw [← pathMatrix_diagonal_difference b d x y m] at h
  exact h
#print axioms Paper7Pruning.pathMatrix_inertia_mono

end Paper7Pruning
