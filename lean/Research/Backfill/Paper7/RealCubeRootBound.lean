import Research.Backfill.Paper7.ChallengeV2

/-! The exact real rpow exponent 1/3, including the zero endpoint. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Section6

theorem le_cube_root_of_cube_le (x y : ℝ) (hx : 0 ≤ x) (h : x^3 ≤ y) :
    x ≤ y^((1 : ℝ)/3) := by
  have hpow := Real.rpow_le_rpow (show 0 ≤ x^3 by positivity) h
    (show (0 : ℝ) ≤ 1/3 by norm_num)
  have hroot : (x^3)^((1 : ℝ)/3) = x := by
    simpa only [one_div, Nat.cast_ofNat] using Real.pow_rpow_inv_natCast (n := 3) hx (by norm_num)
  rwa [hroot] at hpow
#print axioms Paper7Section6.le_cube_root_of_cube_le

end Paper7Section6
