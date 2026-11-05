import Research.Backfill.Paper7.InertiaComparison

set_option autoImplicit false

noncomputable section

namespace Paper7Comparison

open Matrix BackfillPaper7.Challenge Paper7Inertia
open scoped Matrix

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem quadratic_neg_apply (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    (-M).toQuadraticForm' x = -M.toQuadraticForm' x := by
  simp only [quadratic_apply, Matrix.neg_mulVec, dotProduct_neg]
#print axioms Paper7Comparison.quadratic_neg_apply

theorem quadratic_neg (M : Matrix ι ι ℝ) :
    (-M).toQuadraticForm' = -M.toQuadraticForm' := by
  ext x
  exact quadratic_neg_apply M x
#print axioms Paper7Comparison.quadratic_neg

theorem nPos_neg (M : Matrix ι ι ℝ) (hM : M.IsHermitian) : nPos (-M) = nNeg M := by
  rw [nPos_eq_sigPos _ hM.neg, nNeg_eq_sigNeg _ hM, quadratic_neg]
  rfl
#print axioms Paper7Comparison.nPos_neg

theorem nNeg_neg (M : Matrix ι ι ℝ) (hM : M.IsHermitian) : nNeg (-M) = nPos M := by
  have h := nPos_neg (-M) hM.neg
  simpa only [neg_neg] using h.symm
#print axioms Paper7Comparison.nNeg_neg

theorem nZero_neg (M : Matrix ι ι ℝ) (hM : M.IsHermitian) : nZero (-M) = nZero M := by
  have hp := nPos_neg M hM
  have hn := nNeg_neg M hM
  have h₁ := inertia_total M hM
  have h₂ := inertia_total (-M) hM.neg
  omega
#print axioms Paper7Comparison.nZero_neg

theorem nNeg_map_le (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (hf : Function.Injective f)
    (h : ∀ x, B.toQuadraticForm' (f x) ≤ A.toQuadraticForm' x) : nNeg A ≤ nNeg B := by
  rw [← nPos_neg A hA, ← nPos_neg B hB]
  apply nPos_map_le (-A) (-B) hA.neg hB.neg f hf
  intro x
  simpa only [quadratic_neg_apply] using neg_le_neg (h x)
#print axioms Paper7Comparison.nNeg_map_le

theorem nonpos_map_le (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (hf : Function.Injective f)
    (h : ∀ x, B.toQuadraticForm' (f x) ≤ A.toQuadraticForm' x) :
    nNeg A + nZero A ≤ nNeg B + nZero B := by
  have h' := nonneg_map_le (-A) (-B) hA.neg hB.neg f hf (fun x => by
    simpa only [quadratic_neg_apply] using neg_le_neg (h x))
  simpa only [nPos_neg _ hA, nPos_neg _ hB, nZero_neg _ hA, nZero_neg _ hB] using h'
#print axioms Paper7Comparison.nonpos_map_le

/-- Rectangular version: no surjectivity or equality of dimensions is assumed. -/
theorem quadratic_rectangular_congruence (M : Matrix κ κ ℝ) (P : Matrix κ ι ℝ)
    (x : ι → ℝ) :
    (Pᵀ * M * P).toQuadraticForm' x = M.toQuadraticForm' (P *ᵥ x) := by
  simp only [quadratic_apply, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
#print axioms Paper7Comparison.quadratic_rectangular_congruence

/-- The columns are actual coordinate vectors in the larger matrix. -/
def coordinateInclusion (f : ι → κ) : Matrix κ ι ℝ :=
  Matrix.of fun v i => if v = f i then 1 else 0
#print axioms Paper7Comparison.coordinateInclusion

omit [Fintype κ] in
theorem coordinateInclusion_apply (f : ι → κ) (hf : Function.Injective f)
    (x : ι → ℝ) (i : ι) : (coordinateInclusion f *ᵥ x) (f i) = x i := by
  classical
  simp [coordinateInclusion, Matrix.mulVec, dotProduct, hf.eq_iff]
#print axioms Paper7Comparison.coordinateInclusion_apply

omit [Fintype κ] in
theorem coordinateInclusion_injective (f : ι → κ) (hf : Function.Injective f) :
    Function.Injective (coordinateInclusion f).mulVecLin := by
  intro x y h
  funext i
  have hi := congrFun h (f i)
  change (coordinateInclusion f *ᵥ x) (f i) = (coordinateInclusion f *ᵥ y) (f i) at hi
  simpa only [coordinateInclusion_apply f hf] using hi
#print axioms Paper7Comparison.coordinateInclusion_injective

omit [Fintype ι] [DecidableEq ι] in
theorem coordinateInclusion_congruence (M : Matrix κ κ ℝ) (f : ι → κ) :
    (coordinateInclusion f)ᵀ * M * coordinateInclusion f = M.submatrix f f := by
  classical
  apply Matrix.ext
  intro i j
  simp [coordinateInclusion, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply]
#print axioms Paper7Comparison.coordinateInclusion_congruence

/-- A principal submatrix embeds by zero extension, including empty subsets. -/
theorem principal_inertia_bounds (M : Matrix κ κ ℝ) (hM : M.IsHermitian)
    (f : ι → κ) (hf : Function.Injective f) :
    nPos (M.submatrix f f) ≤ nPos M ∧
      nPos (M.submatrix f f) + nZero (M.submatrix f f) ≤ nPos M + nZero M := by
  have hq (x : ι → ℝ) : (M.submatrix f f).toQuadraticForm' x =
      M.toQuadraticForm' ((coordinateInclusion f).mulVecLin x) := by
    rw [← coordinateInclusion_congruence M f]
    exact quadratic_rectangular_congruence M (coordinateInclusion f) x
  exact ⟨nPos_map_le _ M (hM.submatrix f) hM (coordinateInclusion f).mulVecLin
      (coordinateInclusion_injective f hf) (fun x => (hq x).le),
    nonneg_map_le _ M (hM.submatrix f) hM (coordinateInclusion f).mulVecLin
      (coordinateInclusion_injective f hf) (fun x => (hq x).le)⟩
#print axioms Paper7Comparison.principal_inertia_bounds

theorem principal_negative_inertia_bounds (M : Matrix κ κ ℝ) (hM : M.IsHermitian)
    (f : ι → κ) (hf : Function.Injective f) :
    nNeg (M.submatrix f f) ≤ nNeg M ∧
      nNeg (M.submatrix f f) + nZero (M.submatrix f f) ≤ nNeg M + nZero M := by
  have hq (x : ι → ℝ) : M.toQuadraticForm' ((coordinateInclusion f).mulVecLin x) =
      (M.submatrix f f).toQuadraticForm' x := by
    rw [← coordinateInclusion_congruence M f]
    exact (quadratic_rectangular_congruence M (coordinateInclusion f) x).symm
  exact ⟨nNeg_map_le _ M (hM.submatrix f) hM (coordinateInclusion f).mulVecLin
      (coordinateInclusion_injective f hf) (fun x => (hq x).le),
    nonpos_map_le _ M (hM.submatrix f) hM (coordinateInclusion f).mulVecLin
      (coordinateInclusion_injective f hf) (fun x => (hq x).le)⟩
#print axioms Paper7Comparison.principal_negative_inertia_bounds

/-- The explicit graph of minus a linear map, in the original sum coordinates. -/
def schurLift (R : Matrix κ ι ℝ) : (ι → ℝ) →ₗ[ℝ] ((ι ⊕ κ) → ℝ) where
  toFun x := Sum.elim x (-(R *ᵥ x))
  map_add' x y := by
    funext v
    cases v <;> simp [Matrix.mulVec_add, add_comm]
  map_smul' c x := by
    funext v
    cases v <;> simp [Matrix.mulVec_smul]
#print axioms Paper7Comparison.schurLift

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem schurLift_injective (R : Matrix κ ι ℝ) : Function.Injective (schurLift R) := by
  intro x y h
  funext i
  exact congrFun h (Sum.inl i)
#print axioms Paper7Comparison.schurLift_injective

/-- This identity uses the actual block form, not a presumed inertia inequality. -/
theorem schurLift_quadratic (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (C : Matrix κ ι ℝ) (D : Matrix κ κ ℝ) (R : Matrix κ ι ℝ)
    (hDR : D * R = C) (x : ι → ℝ) :
    (Matrix.fromBlocks A B C D).toQuadraticForm' (schurLift R x) =
      (A - B * R).toQuadraticForm' x := by
  have hl : D *ᵥ (R *ᵥ x) = C *ᵥ x := by rw [Matrix.mulVec_mulVec, hDR]
  simp only [quadratic_apply, schurLift, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.fromBlocks_mulVec]
  change Sum.elim x (-(R *ᵥ x)) ⬝ᵥ
      Sum.elim (A *ᵥ x + B *ᵥ (-(R *ᵥ x)))
        (C *ᵥ x + D *ᵥ (-(R *ᵥ x))) = x ⬝ᵥ ((A - B * R) *ᵥ x)
  simp only [Matrix.mulVec_neg, hl, add_neg_cancel,
    sumElim_dotProduct_sumElim, dotProduct_zero, add_zero,
    Matrix.add_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, sub_eq_add_neg]
#print axioms Paper7Comparison.schurLift_quadratic

end Paper7Comparison
