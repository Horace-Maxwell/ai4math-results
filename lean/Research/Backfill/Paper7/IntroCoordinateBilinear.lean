import Research.Backfill.Paper7.MatrixInertiaEmbeddings

/-! Zero extensions preserve actual bilinear forms and their coordinate support. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroStrictCut
open Matrix Paper7Comparison

theorem coordinateInclusion_mixed_congruence
    {V W U : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (f : W → V) (g : U → V) :
    (coordinateInclusion f)ᵀ * M * coordinateInclusion g = M.submatrix f g := by
  ext i j
  simp [coordinateInclusion, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply]
#print axioms Paper7IntroStrictCut.coordinateInclusion_mixed_congruence

theorem coordinateInclusion_bilinear
    {V W U : Type} [Fintype V] [DecidableEq V] [Fintype W] [Fintype U]
    (M : Matrix V V ℝ) (f : W → V) (g : U → V) (x : W → ℝ) (y : U → ℝ) :
    (coordinateInclusion f *ᵥ x) ⬝ᵥ M *ᵥ (coordinateInclusion g *ᵥ y) =
      x ⬝ᵥ M.submatrix f g *ᵥ y := by
  rw [← coordinateInclusion_mixed_congruence M f g]
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
#print axioms Paper7IntroStrictCut.coordinateInclusion_bilinear

theorem coordinateInclusion_dot_self
    {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (f : W → V) (hf : Function.Injective f) (x : W → ℝ) :
    (coordinateInclusion f *ᵥ x) ⬝ᵥ (coordinateInclusion f *ᵥ x) = x ⬝ᵥ x := by
  have h := coordinateInclusion_bilinear (1 : Matrix V V ℝ) f f x x
  simpa only [Matrix.one_mulVec, Matrix.submatrix_one f hf] using h
#print axioms Paper7IntroStrictCut.coordinateInclusion_dot_self

theorem coordinateInclusion_nonnegative
    {V W : Type} [DecidableEq V] [Fintype W]
    (f : W → V) (x : W → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ v, 0 ≤ (coordinateInclusion f *ᵥ x) v := by
  intro v
  change 0 ≤ ∑ i, (if v = f i then (1 : ℝ) else 0) * x i
  apply Finset.sum_nonneg
  intro i _hi
  split_ifs <;> simp only [one_mul, zero_mul, le_refl, hx]
#print axioms Paper7IntroStrictCut.coordinateInclusion_nonnegative

theorem coordinateInclusion_outside_zero
    {V W : Type} [DecidableEq V] [Fintype W]
    (f : W → V) (x : W → ℝ) (v : V) (hv : ∀ i, v ≠ f i) :
    (coordinateInclusion f *ᵥ x) v = 0 := by
  change (∑ i, (if v = f i then (1 : ℝ) else 0) * x i) = 0
  simp only [ite_eq_right (hv _), zero_mul, Finset.sum_const_zero]
#print axioms Paper7IntroStrictCut.coordinateInclusion_outside_zero

end Paper7IntroStrictCut
