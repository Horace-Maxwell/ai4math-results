import Mathlib

/-! The five natural arm-count cases forced by the genuine graph bounds.
Only scalar algebra is used; no graph or certificate table is enumerated. -/
set_option autoImplicit false

namespace Paper7IntroStarExclusion

theorem arm_count_eq_three_of_moment_constraints
    (m : ℕ) (d t : ℝ) (hm : 3 ≤ m) (hm8 : m < 8)
    (hd3 : 3 ≤ d)
    (hd : d = -(m : ℝ) ^ 2 + 9 * (m : ℝ) - 12)
    (ht : t = (13 - 2 * (m : ℝ)) * d - (m : ℝ) ^ 3 + 8 * (m : ℝ) ^ 2 - 36)
    (hlow : d ^ 2 + (m : ℝ) + 2 ≤ t) : m = 3 := by
  have hcases : m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · rfl
  · norm_num at hd ht hlow
    nlinarith only [hd, ht, hlow]
  · norm_num at hd ht hlow
    nlinarith only [hd, ht, hlow]
  · norm_num at hd ht hlow
    nlinarith only [hd, ht, hlow]
  · norm_num at hd
    linarith only [hd, hd3]
#print axioms Paper7IntroStarExclusion.arm_count_eq_three_of_moment_constraints

end Paper7IntroStarExclusion
