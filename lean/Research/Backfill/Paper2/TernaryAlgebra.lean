import Research.Backfill.Paper2.FiniteCoefficients

/-! Algebraic reversion and its integral second-order differential equation.
These are support lemmas, not proofs of the prescribed Fuss-Catalan coefficient formula. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.TernaryAlgebra
open PowerSeries BackfillPaper2.FiniteCoefficients
local notation "D" => PowerSeries.derivative (R := ℤ)

theorem exists_integral_reversion : ∃ V : PowerSeries ℤ,
    constantCoeff V = 0 ∧ coeff 1 V = 1 ∧ V - V ^ 3 = X ∧
      ((X : PowerSeries ℤ) - X ^ 3).subst V = X ∧
      V.subst ((X : PowerSeries ℤ) - X ^ 3) = X := by
  let g : PowerSeries ℤ := X - X ^ 3
  have hg0 : constantCoeff g = 0 := by simp [g]
  have hg1 : coeff 1 g = 1 := by simp [g, coeff_X, coeff_X_pow]
  have hu : IsUnit (coeff 1 g) := by rw [hg1]; exact isUnit_one
  let V := substInvOfIsUnit g hu
  have hv0 : constantCoeff V = 0 := constantCoeff_substInvOfIsUnit g hu
  have hs : HasSubst V := HasSubst.substInvOfIsUnit g hu
  have hR : g.subst V = X := subst_substInvOfIsUnit_right g hg0 hu
  have hL : V.subst g = X := subst_substInvOfIsUnit_left g hg0 hu
  have hv : V - V ^ 3 = X := by
    simpa only [g, subst_sub hs, subst_X hs, subst_pow hs] using hR
  have hv1 : coeff 1 V = 1 := by
    have he := congrArg (coeff 1) hv
    norm_num [pow_succ, coeff_mul_range, Finset.sum_range_succ,
      coeff_zero_eq_constantCoeff_apply, hv0, coeff_X] at he
    exact he
  exact ⟨V, hv0, hv1, hv, hR, hL⟩

theorem reversion_ode (V : PowerSeries ℤ) (h0 : constantCoeff V = 0)
    (hV : V - V ^ 3 = X) :
    (4 - 27 * X ^ 2) * D (D V) - 27 * X * D V + 3 * V = 0 := by
  let u : PowerSeries ℤ := 1 - 3 * V ^ 2
  have hD : u * D V = 1 := by
    have he := congrArg D hV
    simp only [map_sub, derivative_pow, derivative_X] at he
    norm_num at he
    dsimp only [u]
    linear_combination he
  have d3 : D (3 : PowerSeries ℤ) = 0 := by
    change D (C (3 : ℤ)) = 0
    exact derivative_C
  have hdu : D u = -6 * V * D V := by
    dsimp only [u]
    simp only [map_sub, derivative_one, Derivation.leibniz, d3, derivative_pow,
      smul_eq_mul]
    norm_num; ring
  have hDD : u * D (D V) = 6 * V * (D V) ^ 2 := by
    have he := congrArg D hD
    simp only [Derivation.leibniz, derivative_one, smul_eq_mul, hdu] at he
    linear_combination he
  have hu : IsUnit u := isUnit_iff_constantCoeff.mpr (by simp [u, h0])
  apply hu.mul_right_eq_zero.mp
  rw [← hV]
  dsimp only [u] at hD hDD ⊢
  linear_combination (1 - 3 * V ^ 2) ^ 2 * (4 - 3 * V ^ 2) * hDD +
    (6 * V * (4 - 3 * V ^ 2) * ((1 - 3 * V ^ 2) * D V + 1) -
      27 * (V - V ^ 3)) * hD

def euler (V : PowerSeries ℤ) : PowerSeries ℤ := X * D V

theorem coeff_euler (V : PowerSeries ℤ) (n : ℕ) :
    coeff n (euler V) = (n : ℤ) * coeff n V := by
  cases n with
  | zero => simp [euler, coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    change coeff (n + 1) (X * D V) = ((n + 1 : ℕ) : ℤ) * coeff (n + 1) V
    rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

theorem ode_coeff_recurrence (V : PowerSeries ℤ)
    (hODE : (4 - 27 * X ^ 2) * D (D V) - 27 * X * D V + 3 * V = 0) (n : ℕ) :
    4 * ((n + 2 : ℕ) : ℤ) * ((n + 1 : ℕ) : ℤ) * coeff (n + 2) V =
      (27 * (n : ℤ) ^ 2 - 3) * coeff n V := by
  have hE : 4 * (euler (euler V) - euler V) =
      3 * X ^ 2 * (9 * euler (euler V) - V) := by
    dsimp only [euler]
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul, mul_one]
    linear_combination X ^ 2 * hODE
  have he := congrArg (coeff (n + 2)) hE
  have heq : 3 * X ^ 2 * (9 * euler (euler V) - V) =
      3 * (X ^ 2 * (9 * euler (euler V) - V)) := by ring
  rw [heq] at he
  simp only [coeff_ofNat_mul, map_sub, coeff_X_pow_mul, coeff_euler] at he
  push_cast at he ⊢
  linear_combination he

end BackfillPaper2.TernaryAlgebra
#print axioms BackfillPaper2.TernaryAlgebra.exists_integral_reversion
#print axioms BackfillPaper2.TernaryAlgebra.reversion_ode
#print axioms BackfillPaper2.TernaryAlgebra.coeff_euler
#print axioms BackfillPaper2.TernaryAlgebra.ode_coeff_recurrence
