import Research.Backfill.Paper7.InertiaQuadraticBridge

set_option autoImplicit false

noncomputable section

namespace Paper7Admissible

open Matrix BackfillPaper7.Challenge Paper7Inertia
open scoped Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem spectral_unitary_orthogonal (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    (hM.eigenvectorUnitary : Matrix ι ι ℝ) * (hM.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ = 1 ∧
      (hM.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ * (hM.eigenvectorUnitary : Matrix ι ι ℝ) = 1 := by
  constructor
  · simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hM.eigenvectorUnitary
  · simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hM.eigenvectorUnitary
#print axioms Paper7Admissible.spectral_unitary_orthogonal

theorem spectral_unitary_diagonal (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    (hM.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ * M * hM.eigenvectorUnitary =
      Matrix.diagonal hM.eigenvalues := by
  simpa only [Unitary.conjStarAlgAut_star_apply, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    RCLike.ofReal_real_eq_id, Function.id_comp] using
    hM.conjStarAlgAut_star_eigenvectorUnitary
#print axioms Paper7Admissible.spectral_unitary_diagonal

theorem orthogonal_preserves_dot (U : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) (x : ι → ℝ) :
    (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
  have h := quadratic_congruence_apply (1 : Matrix ι ι ℝ) U x
  simpa only [Matrix.mul_one, hU, quadratic_apply, Matrix.one_mulVec] using h.symm
#print axioms Paper7Admissible.orthogonal_preserves_dot

omit [DecidableEq ι] in
theorem abs_vector_dot_self (x : ι → ℝ) :
    (fun i => |x i|) ⬝ᵥ (fun i => |x i|) = x ⬝ᵥ x := by
  simp only [dotProduct, ← pow_two, sq_abs]
#print axioms Paper7Admissible.abs_vector_dot_self

theorem quadratic_constant_diagonal (r : ℝ) (x : ι → ℝ) :
    (Matrix.diagonal (fun _ : ι => r)).toQuadraticForm' x = r * (x ⬝ᵥ x) := by
  simp only [quadratic_apply, dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring
#print axioms Paper7Admissible.quadratic_constant_diagonal

/-- Finite spectral diagonalization supplies the global quadratic upper bound. -/
theorem hermitian_quadratic_upper (M : Matrix ι ι ℝ) (hM : M.IsHermitian) (r : ℝ)
    (hr : ∀ i, hM.eigenvalues i ≤ r) (x : ι → ℝ) :
    M.toQuadraticForm' x ≤ r * (x ⬝ᵥ x) := by
  let U : Matrix ι ι ℝ := hM.eigenvectorUnitary
  let y := Uᵀ *ᵥ x
  have hU := spectral_unitary_orthogonal M hM
  have hxy : U *ᵥ y = x := by
    change U *ᵥ (Uᵀ *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, hU.1, Matrix.one_mulVec]
  have hnorm : y ⬝ᵥ y = x ⬝ᵥ x := by
    have h := orthogonal_preserves_dot U hU.2 y
    rw [hxy] at h
    exact h.symm
  calc
    M.toQuadraticForm' x = (Matrix.diagonal hM.eigenvalues).toQuadraticForm' y := by
      rw [← spectral_unitary_diagonal M hM, quadratic_congruence_apply]
      exact congrArg M.toQuadraticForm' hxy.symm
    _ ≤ r * (y ⬝ᵥ y) := by
      rw [quadratic_diagonal, QuadraticMap.weightedSumSquares_apply, dotProduct,
        Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      change hM.eigenvalues i * (y i * y i) ≤ r * (y i * y i)
      exact mul_le_mul_of_nonneg_right (hr i) (mul_self_nonneg (y i))
    _ = r * (x ⬝ᵥ x) := congrArg (fun t => r*t) hnorm
#print axioms Paper7Admissible.hermitian_quadratic_upper

/-- Equality in the actual maximal form bound implies an eigenvector equation. -/
theorem eigen_of_quadratic_equality (M : Matrix ι ι ℝ) (hM : M.IsHermitian) (r : ℝ)
    (hupper : ∀ y, M.toQuadraticForm' y ≤ r * (y ⬝ᵥ y))
    (x : ι → ℝ) (heq : M.toQuadraticForm' x = r * (x ⬝ᵥ x)) :
    M *ᵥ x = r • x := by
  let B := Matrix.diagonal (fun _ : ι => r) - M
  have hB : B.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((Matrix.isHermitian_diagonal _).sub hM)
    intro y
    have hy := hupper y
    have hdiag := quadratic_constant_diagonal r y
    simp only [quadratic_apply] at hy hdiag
    simpa only [B, star_trivial, Matrix.sub_mulVec, dotProduct_sub, hdiag] using
      sub_nonneg.mpr hy
  have hzero : B *ᵥ x = 0 := by
    apply hB.dotProduct_mulVec_zero_iff.mp
    have hdiag := quadratic_constant_diagonal r x
    simp only [quadratic_apply] at heq hdiag
    simp only [B, star_trivial, Matrix.sub_mulVec, dotProduct_sub, hdiag, heq, sub_self]
  funext i
  have hi := congrFun hzero i
  simp only [B, Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply,
    Matrix.mulVec_diagonal] at hi
  change (M *ᵥ x) i = r * x i
  linarith
#print axioms Paper7Admissible.eigen_of_quadratic_equality

/-- Entrywise nonnegativity bounds the absolute quadratic form by that of |x|. -/
theorem abs_quadratic_le (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 ≤ M i j) (x : ι → ℝ) :
    |M.toQuadraticForm' x| ≤ M.toQuadraticForm' (fun i => |x i|) := by
  simp only [quadratic_apply, Matrix.dot_mulVec_eq_sum_sum]
  calc
    |∑ j, ∑ i, x i * M i j * x j| ≤ ∑ j, |∑ i, x i * M i j * x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ i, |x i * M i j * x j| := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, ∑ i, |x i| * M i j * |x j| := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      simp only [abs_mul, abs_of_nonneg (hM i j)]
#print axioms Paper7Admissible.abs_quadratic_le

theorem hermitian_unit_eigenvector (M : Matrix ι ι ℝ) (hM : M.IsHermitian) (i : ι) :
    ∃ x : ι → ℝ, x ⬝ᵥ x = 1 ∧ M *ᵥ x = hM.eigenvalues i • x := by
  refine ⟨⇑(hM.eigenvectorBasis i), ?_, hM.mulVec_eigenvectorBasis i⟩
  have h := orthogonal_preserves_dot (hM.eigenvectorUnitary : Matrix ι ι ℝ)
    (spectral_unitary_orthogonal M hM).2 (Pi.single i 1)
  rw [hM.eigenvectorUnitary_mulVec] at h
  simpa [dotProduct, Pi.single_apply] using h
#print axioms Paper7Admissible.hermitian_unit_eigenvector

theorem eigenvalue_mem_eigs (M : Matrix ι ι ℝ) (hM : M.IsHermitian) (i : ι) :
    hM.eigenvalues i ∈ eigs M := by
  simp only [eigs, hM.roots_charpoly_eq_eigenvalues, RCLike.ofReal_real_eq_id,
    Function.id_comp, Multiset.mem_map]
  exact ⟨i, by simp, rfl⟩
#print axioms Paper7Admissible.eigenvalue_mem_eigs

theorem eigs_unit_eigenvector (M : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (r : ℝ) (hr : r ∈ eigs M) :
    ∃ x : ι → ℝ, x ⬝ᵥ x = 1 ∧ M *ᵥ x = r • x := by
  simp only [eigs, hM.roots_charpoly_eq_eigenvalues, RCLike.ofReal_real_eq_id,
    Function.id_comp, Multiset.mem_map] at hr
  obtain ⟨i, hi, rfl⟩ := hr
  exact hermitian_unit_eigenvector M hM i
#print axioms Paper7Admissible.eigs_unit_eigenvector

/-- Finite-dimensional Perron existence from actual spectral decomposition.
Strict positivity and simplicity will use the graph's genuine connectedness. -/
theorem exists_nonnegative_top_eigenvector [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : M.IsHermitian) (hNN : ∀ i j, 0 ≤ M i j) :
    ∃ r ∈ eigs M, ∃ v : ι → ℝ,
      (∀ i, 0 ≤ v i) ∧ v ⬝ᵥ v = 1 ∧ M *ᵥ v = r • v ∧ 0 ≤ r ∧
      (∀ x, M.toQuadraticForm' x ≤ r * (x ⬝ᵥ x)) ∧
      (∀ s ∈ eigs M, |s| ≤ r) := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ hM.eigenvalues
    Finset.univ_nonempty
  let r := hM.eigenvalues i
  have hupper : ∀ x, M.toQuadraticForm' x ≤ r * (x ⬝ᵥ x) :=
    hermitian_quadratic_upper M hM r (fun j => hmax j (Finset.mem_univ j))
  obtain ⟨x, hxnorm, hxeig⟩ := hermitian_unit_eigenvector M hM i
  have hxq : M.toQuadraticForm' x = r := by
    rw [quadratic_apply, hxeig, dotProduct_smul, hxnorm]
    simp [r]
  let v : ι → ℝ := fun j => |x j|
  have hvnorm : v ⬝ᵥ v = 1 := (abs_vector_dot_self x).trans hxnorm
  have hvq : M.toQuadraticForm' v = r := by
    have hlo := (le_abs_self (M.toQuadraticForm' x)).trans (abs_quadratic_le M hNN x)
    rw [hxq] at hlo
    have hhi := hupper v
    rw [hvnorm, mul_one] at hhi
    exact le_antisymm hhi hlo
  have hveig : M *ᵥ v = r • v := eigen_of_quadratic_equality M hM r hupper v (by
    rw [hvnorm, mul_one]
    exact hvq)
  have hr0 : 0 ≤ r := by
    rw [← hvq, quadratic_apply, Matrix.dot_mulVec_eq_sum_sum]
    exact Finset.sum_nonneg (fun j hj => Finset.sum_nonneg (fun k hk =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (hNN k j)) (abs_nonneg _)))
  refine ⟨r, eigenvalue_mem_eigs M hM i, v, (fun j => abs_nonneg (x j)),
    hvnorm, hveig, hr0, hupper, ?_⟩
  intro s hs
  obtain ⟨w, hwnorm, hweig⟩ := eigs_unit_eigenvector M hM s hs
  have hwq : M.toQuadraticForm' w = s := by
    rw [quadratic_apply, hweig, dotProduct_smul, hwnorm]
    simp
  have h₁ := abs_quadratic_le M hNN w
  have h₂ := hupper (fun j => |w j|)
  rw [abs_vector_dot_self, hwnorm, mul_one] at h₂
  rw [hwq] at h₁
  exact h₁.trans h₂
#print axioms Paper7Admissible.exists_nonnegative_top_eigenvector

end Paper7Admissible
