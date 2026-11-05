import Research.Backfill.Paper7.IntroRadiusThreeScaledPolynomial

/-! A zero quadratic value of a real symmetric scaled idempotent forces
the actual vector into its kernel. No positivity or rank premise is needed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroFourProjector
open Matrix

theorem symmetric_scaled_idempotent_quadratic_zero
    {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : M.IsSymm) (r : ℝ)
    (hsq : M ^ 2 = r • M) (v : V → ℝ)
    (hz : v ⬝ᵥ M *ᵥ v = 0) : M *ᵥ v = 0 := by
  apply dotProduct_self_eq_zero.mp
  calc
    (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ M *ᵥ (M *ᵥ v) := hM.dotProduct_mulVec_comm
    _ = v ⬝ᵥ (M ^ 2) *ᵥ v := by rw [pow_two, ← Matrix.mulVec_mulVec]
    _ = r * (v ⬝ᵥ M *ᵥ v) := by
      rw [hsq, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    _ = 0 := by rw [hz, mul_zero]
#print axioms Paper7IntroFourProjector.symmetric_scaled_idempotent_quadratic_zero

end Paper7IntroFourProjector
