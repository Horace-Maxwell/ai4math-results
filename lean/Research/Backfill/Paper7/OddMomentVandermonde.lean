import Mathlib

/-! The shifted Vandermonde argument with the additional node 1. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Paper7OddIntegral

theorem shifted_moments_force_zero_fin {n : ℕ} (w a : Fin n → ℝ)
    (hw : Function.Injective w) (h1 : ∀ i, w i ≠ 1)
    (hm : ∀ j : ℕ, 1 ≤ j → j ≤ n → ∑ i, a i * (w i ^ j - 1) = 0) : a = 0 := by
  let nodes : Fin (n + 1) → ℝ := Fin.cons 1 w
  let weights : Fin (n + 1) → ℝ := Fin.cons (-(∑ i, a i)) a
  have hnodes : Function.Injective nodes := by
    apply Fin.cons_injective_of_injective _ hw
    rintro ⟨i, hi⟩
    exact h1 i hi
  have hmom (j : Fin (n + 1)) : ∑ i, weights i * nodes i ^ (j : ℕ) = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [nodes, weights, Fin.cons_zero, Fin.cons_succ, one_pow, mul_one]
    by_cases hj : (j : ℕ) = 0
    · simp only [hj, pow_zero, mul_one, neg_add_cancel]
    · have h := hm (j : ℕ) (by omega) (by omega)
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib] at h
      linarith
  have hz : weights = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hnodes hmom
  funext i
  have hi := congrFun hz i.succ
  simpa only [weights, Fin.cons_succ, Pi.zero_apply] using hi
#print axioms Paper7OddIntegral.shifted_moments_force_zero_fin

theorem shifted_moments_force_zero {ι : Type} [Fintype ι] (w a : ι → ℝ)
    (hw : Function.Injective w) (h1 : ∀ i, w i ≠ 1)
    (hm : ∀ j : ℕ, 1 ≤ j → j ≤ Fintype.card ι →
      ∑ i, a i * (w i ^ j - 1) = 0) : a = 0 := by
  classical
  let e := Fintype.equivFin ι
  have hz : (fun i => a (e.symm i)) = 0 := by
    apply shifted_moments_force_zero_fin (fun i => w (e.symm i))
      (fun i => a (e.symm i)) (hw.comp e.symm.injective) (fun i => h1 (e.symm i))
    intro j hj hn
    rw [e.symm.sum_comp (fun i => a i * (w i ^ j - 1))]
    exact hm j hj hn
  funext i
  have hi := congrFun hz (e i)
  simpa only [Equiv.symm_apply_apply, Pi.zero_apply] using hi
#print axioms Paper7OddIntegral.shifted_moments_force_zero

/-- Any finite positive support producing the first nonzero odd moment must
have at least the specified cardinality; zero coefficients are permitted. -/
theorem odd_moment_support_card_lower (S : Finset ℤ) (a : ℤ → ℝ) (g : ℕ)
    (hpos : ∀ v ∈ S, 2 ≤ v)
    (hbelow : ∀ j : ℕ, 1 ≤ j → 2 * j + 1 < g →
      ∑ v ∈ S, a v * ((v : ℝ) ^ (2 * j + 1) - v) = 0)
    (htop : (∑ v ∈ S, a v * ((v : ℝ) ^ g - v)) ≠ 0) :
    (g - 1) / 2 ≤ S.card := by
  classical
  by_contra hcard
  have hsmall : S.card < (g - 1) / 2 := lt_of_not_ge hcard
  let w : S → ℝ := fun v => (v.val : ℝ) ^ 2
  let c : S → ℝ := fun v => a v.val * (v.val : ℝ)
  have hw : Function.Injective w := by
    intro u v huv
    have hu : (2 : ℝ) ≤ (u.val : ℝ) := by exact_mod_cast hpos u.val u.property
    have hv : (2 : ℝ) ≤ (v.val : ℝ) := by exact_mod_cast hpos v.val v.property
    have huv' : (u.val : ℝ) = (v.val : ℝ) := by
      change (u.val : ℝ) ^ 2 = (v.val : ℝ) ^ 2 at huv
      exact (sq_eq_sq₀ (by linarith) (by linarith)).mp huv
    apply Subtype.ext
    exact_mod_cast huv'
  have h1 : ∀ v, w v ≠ 1 := by
    intro v hv
    have hposR : (2 : ℝ) ≤ (v.val : ℝ) := by exact_mod_cast hpos v.val v.property
    change (v.val : ℝ) ^ 2 = 1 at hv
    nlinarith
  have hm : ∀ j : ℕ, 1 ≤ j → j ≤ Fintype.card S →
      ∑ v : S, c v * (w v ^ j - 1) = 0 := by
    intro j hj hjs
    have hjs' : j ≤ S.card := by simpa only [Fintype.card_coe] using hjs
    have hlow : 2 * j + 1 < g := by omega
    have h := hbelow j hj hlow
    rw [← Finset.sum_coe_sort] at h
    calc
      _ = ∑ v : S, a v.val * ((v.val : ℝ) ^ (2 * j + 1) - v.val) := by
        apply Finset.sum_congr rfl
        intro v _
        simp only [c, w, pow_add, pow_mul, pow_one]
        ring
      _ = 0 := h
  have hc : c = 0 := shifted_moments_force_zero w c hw h1 hm
  have ha (v : ℤ) (hv : v ∈ S) : a v = 0 := by
    have he := congrFun hc ⟨v, hv⟩
    change a v * (v : ℝ) = 0 at he
    have hvpos : (0 : ℝ) < (v : ℝ) := by
      have : (2 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hpos v hv
      linarith
    exact (mul_eq_zero.mp he).resolve_right (ne_of_gt hvpos)
  apply htop
  apply Finset.sum_eq_zero
  intro v hv
  rw [ha v hv, zero_mul]
#print axioms Paper7OddIntegral.odd_moment_support_card_lower

end Paper7OddIntegral
