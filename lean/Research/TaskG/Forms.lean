import Research.TaskG.Data

/-! Associating forms of the four-dimensional Task G algebra. -/
set_option autoImplicit false
namespace TaskG.Proof
open AxialMSZ.Challenge

theorem beta_symmetric (u v : V) : β u v = β v u := by
  simp only [β_apply]
  ring

theorem beta_nonzero : β ≠ 0 := by
  intro h
  have h0 := congrArg (fun q : V →ₗ[K] V →ₗ[K] K => q (e 0) (e 0)) h
  norm_num [β_apply, e, Pi.single_apply] at h0

theorem beta_frobenius : IsFrobeniusForm μ β := by
  intro u v w
  simp [β_apply, μ_apply]
  ring

private theorem vector_expand (v : V) :
    v = v 0 • e 0 + v 1 • e 1 + v 2 • e 2 + v 3 • e 3 := by
  ext i
  fin_cases i <;> simp [e]

private theorem mu_e_e (i j : Fin 4) : μ (e i) (e j) = T i j := by
  exact μ_e i j

private theorem form_equation (γ : V →ₗ[K] V →ₗ[K] K)
    (hγ : IsFrobeniusForm μ γ) (i j k : Fin 4) :
    (T i j 0 * γ (e 0) (e k) + T i j 1 * γ (e 1) (e k) +
      T i j 2 * γ (e 2) (e k) + T i j 3 * γ (e 3) (e k)) =
    (T j k 0 * γ (e i) (e 0) + T j k 1 * γ (e i) (e 1) +
      T j k 2 * γ (e i) (e 2) + T j k 3 * γ (e i) (e 3)) := by
  have h := hγ (e i) (e j) (e k)
  rw [mu_e_e, mu_e_e, vector_expand (T i j), vector_expand (T j k)] at h
  simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul] using h

private theorem eq_zero_of_two_mul {x : K} (h : 2 * x = 0) : x = 0 :=
  (mul_eq_zero.mp h).resolve_left (by decide)

/-- Every associating form is diagonal in the idempotent basis, without a symmetry assumption. -/
theorem form_off_diagonal (γ : V →ₗ[K] V →ₗ[K] K) (hγ : IsFrobeniusForm μ γ) :
    ∀ i j : Fin 4, i ≠ j → γ (e i) (e j) = 0 := by
  have h001 := form_equation γ hγ 0 0 1
  have h002 := form_equation γ hγ 0 0 2
  have h003 := form_equation γ hγ 0 0 3
  have h110 := form_equation γ hγ 1 1 0
  have h112 := form_equation γ hγ 1 1 2
  have h113 := form_equation γ hγ 1 1 3
  have h220 := form_equation γ hγ 2 2 0
  have h221 := form_equation γ hγ 2 2 1
  have h223 := form_equation γ hγ 2 2 3
  have h330 := form_equation γ hγ 3 3 0
  have h331 := form_equation γ hγ 3 3 1
  have h332 := form_equation γ hγ 3 3 2
  norm_num [T] at h001 h002 h003 h110 h112 h113 h220 h221 h223 h330 h331 h332
  have h01 : γ (e 0) (e 1) = 0 := eq_zero_of_two_mul (by linear_combination h001 + h002)
  have h02 : γ (e 0) (e 2) = 0 := eq_zero_of_two_mul (by linear_combination -h001 - h003)
  have h03 : γ (e 0) (e 3) = 0 := eq_zero_of_two_mul (by linear_combination h002 + h003)
  have h10 : γ (e 1) (e 0) = 0 := eq_zero_of_two_mul (by linear_combination h110 + h113)
  have h12 : γ (e 1) (e 2) = 0 := eq_zero_of_two_mul (by linear_combination h112 + h113)
  have h13 : γ (e 1) (e 3) = 0 := eq_zero_of_two_mul (by linear_combination -h110 - h112)
  have h20 : γ (e 2) (e 0) = 0 := eq_zero_of_two_mul (by linear_combination -h221 - h223)
  have h21 : γ (e 2) (e 1) = 0 := eq_zero_of_two_mul (by linear_combination h220 + h221)
  have h23 : γ (e 2) (e 3) = 0 := eq_zero_of_two_mul (by linear_combination h220 + h223)
  have h30 : γ (e 3) (e 0) = 0 := eq_zero_of_two_mul (by linear_combination h330 + h331)
  have h31 : γ (e 3) (e 1) = 0 := eq_zero_of_two_mul (by linear_combination -h330 - h332)
  have h32 : γ (e 3) (e 2) = 0 := eq_zero_of_two_mul (by linear_combination h331 + h332)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
  | exact (hij rfl).elim
  | assumption

/-- All associating bilinear forms are scalar multiples of the displayed form. -/
theorem form_scalar (γ : V →ₗ[K] V →ₗ[K] K) (hγ : IsFrobeniusForm μ γ) :
    γ = γ (e 0) (e 0) • β := by
  have h0 := form_off_diagonal γ hγ
  have h012 := form_equation γ hγ 0 1 2
  have h013 := form_equation γ hγ 0 1 3
  have h021 := form_equation γ hγ 0 2 1
  have hz32 := h0 3 2 (by decide)
  have hz03 := h0 0 3 (by decide)
  have hz23 := h0 2 3 (by decide)
  have hz02 := h0 0 2 (by decide)
  have hz31 := h0 3 1 (by decide)
  norm_num [T, hz32, hz03] at h012
  norm_num [T, hz23, hz02] at h013
  norm_num [T, hz31, hz03] at h021
  have h11 : γ (e 1) (e 1) = -γ (e 0) (e 0) := by linear_combination -h021
  have h22 : γ (e 2) (e 2) = γ (e 0) (e 0) := h012
  have h33 : γ (e 3) (e 3) = -γ (e 0) (e 0) := h013
  apply LinearMap.ext_basis (Pi.basisFun K (Fin 4)) (Pi.basisFun K (Fin 4))
  intro i j
  simp only [Pi.basisFun_apply]
  change γ (e i) (e j) = γ (e 0) (e 0) * β (e i) (e j)
  have hb : ∀ i j : Fin 4,
      β (e i) (e j) = if i = j then (![1,-1,1,-1] : V) i else 0 := by
    decide +kernel
  rw [hb]
  by_cases hij : i = j
  · subst j
    fin_cases i
    · simp
    · simpa using h11
    · simpa using h22
    · simpa using h33
  · rw [ite_eq_right hij, mul_zero]
    exact h0 i j hij

theorem beta_form_space : TaskG.Challenge.FormSpaceOneDimensional μ β := by
  refine ⟨beta_nonzero, ?_⟩
  intro γ hγ
  exact ⟨γ (e 0) (e 0), form_scalar γ hγ⟩

#print axioms beta_symmetric
#print axioms beta_nonzero
#print axioms beta_frobenius
#print axioms form_scalar
#print axioms beta_form_space
end TaskG.Proof
