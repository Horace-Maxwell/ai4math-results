import Research.Backfill.Paper7.PruningMatrixMono

/-! The m=1 support-change case. Kq is the original full Fin b support;
the last vertex is excluded only after proving it is unassigned when d<b. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace Paper7Pruning
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

def pruningPathSet (b : ℕ) : Finset (Fin b) := Finset.univ.filter (fun i => i.val < b-1)
#print axioms Paper7Pruning.pruningPathSet

theorem prefix_Kq_subset_path (b d : ℕ) (x : PQ b) (hd : d < b) :
    Kq b («prefix» d x).2 ⊆ pruningPathSet b := by
  intro i hi
  have hq : 0 < («prefix» d x).2 i := (Finset.mem_filter.mp hi).2
  have hid : i.val < d := by
    by_contra h
    simp only [«prefix», ite_eq_right h] at hq
    omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by omega⟩
#print axioms Paper7Pruning.prefix_Kq_subset_path

theorem rIndex_card_partition (b d : ℕ) (x : PQ b) (hd : d < b) :
    Fintype.card (RIndex b d x) + (Kq b («prefix» d x).2).card = (pruningPathSet b).card := by
  classical
  have hset : Finset.univ.filter
      (fun i : Fin b => i.val < b-1 ∧ («prefix» d x).2 i = 0) =
      pruningPathSet b \ Kq b («prefix» d x).2 := by
    ext i
    simp only [pruningPathSet, Kq, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_sdiff]
    omega
  change Fintype.card {i : Fin b // i.val < b-1 ∧ («prefix» d x).2 i = 0} + _ = _
  rw [Fintype.card_subtype, hset]
  exact Finset.card_sdiff_add_card_eq_card (prefix_Kq_subset_path b d x hd)
#print axioms Paper7Pruning.rIndex_card_partition

def rIndexEmbedding (b d : ℕ) (x y : PQ b)
    (hxy : ∀ i, x.1 i ≤ y.1 i ∧ x.2 i ≤ y.2 i) : RIndex b d y ↪ RIndex b d x where
  toFun i := ⟨i.val, i.property.1, by
    have h := (prefix_coordinate_mono b d x y hxy i.val).2
    have hz := i.property.2
    omega⟩
  inj' := by
    intro i j h
    exact Subtype.ext (congrArg (fun z : RIndex b d x => z.val) h)
#print axioms Paper7Pruning.rIndexEmbedding

theorem rPathMatrix_isHermitian (b d : ℕ) (x : PQ b) :
    (rPathMatrix b d x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp [rPathMatrix]
  · simp [rPathMatrix, h, Ne.symm h, or_comm]
#print axioms Paper7Pruning.rPathMatrix_isHermitian

theorem rPathMatrix_principal_difference (b d : ℕ) (x y : PQ b)
    (hxy : ∀ i, x.1 i ≤ y.1 i ∧ x.2 i ≤ y.2 i) :
    rPathMatrix b d y =
      (rPathMatrix b d x).submatrix (rIndexEmbedding b d x y hxy)
        (rIndexEmbedding b d x y hxy) +
      Matrix.diagonal (fun i : RIndex b d y =>
        ((«prefix» d y).1 i.val : ℝ) - ((«prefix» d x).1 i.val : ℝ)) := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp only [rPathMatrix, Matrix.submatrix_apply, Matrix.add_apply,
      ite_true, Matrix.diagonal_apply_eq]
    change ((«prefix» d y).1 i.val : ℝ)-1 =
      ((«prefix» d x).1 i.val : ℝ)-1 +
        (((«prefix» d y).1 i.val : ℝ)-((«prefix» d x).1 i.val : ℝ))
    ring
  · have he : rIndexEmbedding b d x y hxy i ≠ rIndexEmbedding b d x y hxy j :=
      (rIndexEmbedding b d x y hxy).injective.ne h
    simp only [rPathMatrix, Matrix.submatrix_apply, Matrix.add_apply,
      ite_eq_right h, ite_eq_right he, Matrix.diagonal_apply_ne _ h, add_zero]
    rfl
#print axioms Paper7Pruning.rPathMatrix_principal_difference

theorem rPathMatrix_principal_mono (b d : ℕ) (x y : PQ b)
    (hxy : ∀ i, x.1 i ≤ y.1 i ∧ x.2 i ≤ y.2 i) :
    nPos ((rPathMatrix b d x).submatrix (rIndexEmbedding b d x y hxy)
      (rIndexEmbedding b d x y hxy)) ≤ nPos (rPathMatrix b d y) := by
  have h := (diagonal_add_inertia_mono
    ((rPathMatrix b d x).submatrix (rIndexEmbedding b d x y hxy)
      (rIndexEmbedding b d x y hxy))
    ((rPathMatrix_isHermitian b d x).submatrix (rIndexEmbedding b d x y hxy))
    (fun i : RIndex b d y =>
      ((«prefix» d y).1 i.val : ℝ) - ((«prefix» d x).1 i.val : ℝ))
    (fun i => by
      apply sub_nonneg.mpr
      exact_mod_cast (prefix_coordinate_mono b d x y hxy i.val).1)).1
  rw [← rPathMatrix_principal_difference b d x y hxy] at h
  exact h
#print axioms Paper7Pruning.rPathMatrix_principal_mono

theorem lowerGT_one_mono (b d : ℕ) (x y : PQ b) (hd : d < b)
    (hxy : ∀ i, x.1 i ≤ y.1 i ∧ x.2 i ≤ y.2 i) :
    lowerGT b d x 1 ≤ lowerGT b d y 1 := by
  have hdelete := principal_positive_upper (rPathMatrix b d x) (rPathMatrix_isHermitian b d x)
    (rIndexEmbedding b d x y hxy) (rIndexEmbedding b d x y hxy).injective
  have hdiag := rPathMatrix_principal_mono b d x y hxy
  have hxcard := rIndex_card_partition b d x hd
  have hycard := rIndex_card_partition b d y hd
  simp only [lowerGT, ite_true]
  omega
#print axioms Paper7Pruning.lowerGT_one_mono

end Paper7Pruning
