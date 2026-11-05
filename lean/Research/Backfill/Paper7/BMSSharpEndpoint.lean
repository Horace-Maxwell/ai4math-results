import Research.Backfill.Paper7.ChallengeV2

/-! Exact sharp endpoint and its terminal-path resolvent coefficient. -/
set_option autoImplicit false
noncomputable section
namespace Paper7BMS

def rho : ℝ := 2 * Real.cos (Real.pi / 9)
#print axioms Paper7BMS.rho

theorem one_lt_rho : 1 < rho := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := Real.pi / 9)
    (y := Real.pi / 3) (by positivity) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])
  rw [Real.cos_pi_div_three] at h
  dsimp only [rho]
  linarith
#print axioms Paper7BMS.one_lt_rho

theorem rho_lt_two : rho < 2 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := Real.pi / 9)
    (le_refl 0) (by linarith [Real.pi_pos]) (by positivity)
  rw [Real.cos_zero] at h
  dsimp only [rho]
  linarith
#print axioms Paper7BMS.rho_lt_two

theorem rho_cubic : rho ^ 3 - 3 * rho - 1 = 0 := by
  have h := Real.cos_three_mul (Real.pi / 9)
  rw [show 3 * (Real.pi / 9) = Real.pi / 3 by ring, Real.cos_pi_div_three] at h
  dsimp only [rho]
  nlinarith
#print axioms Paper7BMS.rho_cubic

theorem two_lt_rho_sq : 2 < rho ^ 2 := by
  have hp : 0 < rho := lt_trans (by norm_num) one_lt_rho
  have h3 : 3 < rho ^ 2 := by
    by_contra h
    have hn : rho * (rho ^ 2 - 3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hp.le (by linarith)
    nlinarith [rho_cubic]
  linarith
#print axioms Paper7BMS.two_lt_rho_sq

def terminalResolvent (x : ℝ) : ℝ := (x ^ 2 - 1) / (x * (2 - x ^ 2))
#print axioms Paper7BMS.terminalResolvent

theorem terminalResolvent_one : terminalResolvent 1 = 0 := by
  norm_num [terminalResolvent]
#print axioms Paper7BMS.terminalResolvent_one

theorem rho_resolvent_denominator_ne : rho * (2 - rho ^ 2) ≠ 0 := by
  apply mul_ne_zero
  · have := one_lt_rho
    linarith
  · have := two_lt_rho_sq
    linarith
#print axioms Paper7BMS.rho_resolvent_denominator_ne

theorem terminalResolvent_rho : terminalResolvent rho = 1 - rho := by
  apply (div_eq_iff rho_resolvent_denominator_ne).mpr
  have h : (rho - 1) * (rho ^ 3 - 3 * rho - 1) = 0 := by
    rw [rho_cubic, mul_zero]
  nlinarith
#print axioms Paper7BMS.terminalResolvent_rho

end Paper7BMS
