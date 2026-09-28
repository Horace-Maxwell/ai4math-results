import Research.AxialMSZ.Proof.ExDBase

/-! An explicit associating bilinear form, nonzero on every generating axis of ExD. -/
set_option autoImplicit false
namespace CodexAxial.DecomposableExample
open AxialMSZ.Challenge

def beta : A →ₗ[ℚ] A →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun u v =>
    u 0*v 0 + u 1*v 1 + u 2*v 2 + u 3*v 3 +
    (u 0*v 1+u 1*v 0+u 0*v 2+u 2*v 0+u 1*v 2+u 2*v 1)/4)
    (by intro u w v; simp only [Pi.add_apply]; ring)
    (by intro r u v; simp only [Pi.smul_apply,smul_eq_mul]; ring)
    (by intro u v w; simp only [Pi.add_apply]; ring)
    (by intro r u v; simp only [Pi.smul_apply,smul_eq_mul]; ring)

theorem beta_apply (u v : A) : beta u v =
    u 0*v 0 + u 1*v 1 + u 2*v 2 + u 3*v 3 +
    (u 0*v 1+u 1*v 0+u 0*v 2+u 2*v 0+u 1*v 2+u 2*v 1)/4 := rfl

theorem beta_frobenius : IsFrobeniusForm ExD.μ beta := by
  intro u v w
  simp only [beta_apply,mul_formula]
  simp
  ring

theorem beta_on_axes : ∀ z ∈ ExD.X, beta z z ≠ 0 := by
  rintro z (rfl | rfl | rfl) <;> norm_num [beta_apply,e,Pi.single_apply]

theorem frobenius_exists :
    ∃ β : A →ₗ[ℚ] A →ₗ[ℚ] ℚ, IsFrobeniusForm ExD.μ β ∧ ∀ z ∈ ExD.X, β z z ≠ 0 :=
  ⟨beta,beta_frobenius,beta_on_axes⟩

#print axioms frobenius_exists
end CodexAxial.DecomposableExample
