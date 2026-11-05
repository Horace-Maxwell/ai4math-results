import Research.Backfill.Paper7.ChallengeV2

set_option autoImplicit false

noncomputable section

namespace Paper7Inertia

open Matrix BackfillPaper7.Challenge
open scoped Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quadratic_apply (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    M.toQuadraticForm' x = x ⬝ᵥ (M *ᵥ x) := by
  exact Matrix.toLinearMap₂'_apply' M x x
#print axioms Paper7Inertia.quadratic_apply

theorem quadratic_diagonal (w : ι → ℝ) :
    (Matrix.diagonal w).toQuadraticForm' = QuadraticMap.weightedSumSquares ℝ w := by
  ext x
  simp only [quadratic_apply, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
    dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.mulVec_diagonal]
  ring
#print axioms Paper7Inertia.quadratic_diagonal

def matrixLinearEquiv (P Q : Matrix ι ι ℝ) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) where
  toFun := P.mulVec
  invFun := Q.mulVec
  left_inv x := by rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
  right_inv x := by rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  map_add' x y := Matrix.mulVec_add P x y
  map_smul' c x := Matrix.mulVec_smul P c x
#print axioms Paper7Inertia.matrixLinearEquiv

theorem quadratic_congruence_apply (M P : Matrix ι ι ℝ) (x : ι → ℝ) :
    (Pᵀ * M * P).toQuadraticForm' x = M.toQuadraticForm' (P *ᵥ x) := by
  simp only [quadratic_apply, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
#print axioms Paper7Inertia.quadratic_congruence_apply

theorem quadratic_equivalent_congruence (M P Q : Matrix ι ι ℝ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    M.toQuadraticForm'.Equivalent (Pᵀ * M * P).toQuadraticForm' := by
  apply QuadraticMap.Equivalent.symm
  refine ⟨{ matrixLinearEquiv P Q hPQ hQP with map_app' := ?_ }⟩
  intro x
  exact (quadratic_congruence_apply M P x).symm
#print axioms Paper7Inertia.quadratic_equivalent_congruence

theorem quadratic_equivalent_eigenvalues (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    M.toQuadraticForm'.Equivalent
      (QuadraticMap.weightedSumSquares ℝ hM.eigenvalues) := by
  let U : Matrix ι ι ℝ := hM.eigenvectorUnitary
  have hU : U * Uᵀ = 1 := by
    simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Unitary.coe_mul_star_self hM.eigenvectorUnitary)
  have hU' : Uᵀ * U = 1 := by
    simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Unitary.coe_star_mul_self hM.eigenvectorUnitary)
  have hd : Uᵀ * M * U = Matrix.diagonal hM.eigenvalues := by
    simpa only [Unitary.conjStarAlgAut_star_apply, U, Unitary.coe_star,
      Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id,
      Function.id_comp] using hM.conjStarAlgAut_star_eigenvectorUnitary
  have he := quadratic_equivalent_congruence M U Uᵀ hU hU'
  rw [hd, quadratic_diagonal] at he
  exact he
#print axioms Paper7Inertia.quadratic_equivalent_eigenvalues

theorem nPos_eq_eigenvalue_card (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    nPos M = {i | 0 < hM.eigenvalues i}.ncard := by
  classical
  simp only [nPos, eigs, hM.roots_charpoly_eq_eigenvalues, RCLike.ofReal_real_eq_id,
    Function.id_comp, Multiset.filter_map, Multiset.card_map]
  change (Finset.univ.filter (fun i => 0 < hM.eigenvalues i)).card = _
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i
  simp
#print axioms Paper7Inertia.nPos_eq_eigenvalue_card

theorem nNeg_eq_eigenvalue_card (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    nNeg M = {i | hM.eigenvalues i < 0}.ncard := by
  classical
  simp only [nNeg, eigs, hM.roots_charpoly_eq_eigenvalues, RCLike.ofReal_real_eq_id,
    Function.id_comp, Multiset.filter_map, Multiset.card_map]
  change (Finset.univ.filter (fun i => hM.eigenvalues i < 0)).card = _
  rw [← Set.ncard_coe_finset]
  congr 1
  ext i
  simp
#print axioms Paper7Inertia.nNeg_eq_eigenvalue_card

theorem nPos_eq_sigPos (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    nPos M = sigPos M.toQuadraticForm' := by
  rw [nPos_eq_eigenvalue_card M hM]
  exact (QuadraticForm.sigPos_of_equiv_weightedSumSquares
    (quadratic_equivalent_eigenvalues M hM)).symm
#print axioms Paper7Inertia.nPos_eq_sigPos

theorem nNeg_eq_sigNeg (M : Matrix ι ι ℝ) (hM : M.IsHermitian) :
    nNeg M = sigNeg M.toQuadraticForm' := by
  rw [nNeg_eq_eigenvalue_card M hM]
  exact (QuadraticForm.sigNeg_of_equiv_weightedSumSquares
    (quadratic_equivalent_eigenvalues M hM)).symm
#print axioms Paper7Inertia.nNeg_eq_sigNeg

theorem inertia_congruence (M P Q : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    nPos (Pᵀ * M * P) = nPos M ∧ nNeg (Pᵀ * M * P) = nNeg M := by
  have hC : (Pᵀ * M * P).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.isHermitian_conjTranspose_mul_mul P hM)
  have he := quadratic_equivalent_congruence M P Q hPQ hQP
  constructor
  · rw [nPos_eq_sigPos _ hC, nPos_eq_sigPos _ hM]
    exact he.sigPos_eq.symm
  · rw [nNeg_eq_sigNeg _ hC, nNeg_eq_sigNeg _ hM]
    exact he.sigNeg_eq.symm
#print axioms Paper7Inertia.inertia_congruence

theorem inertia_diagonal (w : ι → ℝ) :
    nPos (Matrix.diagonal w) = {i | 0 < w i}.ncard ∧
      nNeg (Matrix.diagonal w) = {i | w i < 0}.ncard := by
  have hd : (Matrix.diagonal w).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · simp only [Matrix.diagonal_apply_ne _ (Ne.symm hij),
        Matrix.diagonal_apply_ne _ hij, star_zero]
  constructor
  · calc
      nPos (Matrix.diagonal w) = sigPos (Matrix.diagonal w).toQuadraticForm' :=
        nPos_eq_sigPos _ hd
      _ = sigPos (QuadraticMap.weightedSumSquares ℝ w) :=
        congrArg (fun Q : QuadraticForm ℝ (ι → ℝ) => sigPos Q) (quadratic_diagonal w)
      _ = {i | 0 < w i}.ncard :=
        QuadraticForm.sigPos_weightedSumSquares (𝕜 := ℝ) (w := w)
  · calc
      nNeg (Matrix.diagonal w) = sigNeg (Matrix.diagonal w).toQuadraticForm' :=
        nNeg_eq_sigNeg _ hd
      _ = sigNeg (QuadraticMap.weightedSumSquares ℝ w) :=
        congrArg (fun Q : QuadraticForm ℝ (ι → ℝ) => sigNeg Q) (quadratic_diagonal w)
      _ = {i | w i < 0}.ncard :=
        QuadraticForm.sigNeg_weightedSumSquares (𝕜 := ℝ) (w := w)
#print axioms Paper7Inertia.inertia_diagonal

theorem inertia_block_diagonal {κ : Type} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (D : Matrix κ κ ℝ) :
    nPos (Matrix.fromBlocks A 0 0 D) = nPos A + nPos D ∧
      nNeg (Matrix.fromBlocks A 0 0 D) = nNeg A + nNeg D := by
  have hr : (Matrix.fromBlocks A 0 0 D).charpoly.roots =
      A.charpoly.roots + D.charpoly.roots := by
    rw [Matrix.charpoly_fromBlocks_zero₁₂,
      Polynomial.roots_mul (mul_ne_zero A.charpoly_monic.ne_zero D.charpoly_monic.ne_zero)]
  constructor <;> simp only [nPos, nNeg, eigs, hr, Multiset.filter_add, Multiset.card_add]
#print axioms Paper7Inertia.inertia_block_diagonal

end Paper7Inertia
