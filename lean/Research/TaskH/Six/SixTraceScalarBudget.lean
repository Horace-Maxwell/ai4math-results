import Mathlib

/-!
Exact rational scalar tail of the six-cycle trace estimate. It contains no
graph assumptions. The bare-graph application must independently retain
Nonempty V, n<=37, actual degrees and the full true-cycle trace identity.
-/

set_option autoImplicit false

namespace TaskH.Six

theorem trace_six_scalar_lower_bound (n h : ℝ)
    (hn : n ≤ 37) (hh : 121 ≤ h) :
    (14586215 / 28 : ℝ) ≤
      (8 * h + 33) ^ 2 + n * (-(10503 / 28) * h + 453407 / 14) := by
  let B : ℝ := -(10503 / 28) * h + 453407 / 14
  have hB : B ≤ 0 := by
    dsimp [B]
    nlinarith
  have hm : 37 * B ≤ n * B := mul_le_mul_of_nonpos_right hn hB
  have he : (8 * h + 33) ^ 2 + 37 * B =
      14586215 / 28 + (59837 / 28) * (h - 121) + 64 * (h - 121) ^ 2 := by
    dsimp [B]
    ring
  have hb : (14586215 / 28 : ℝ) ≤ (8 * h + 33) ^ 2 + 37 * B := by
    rw [he]
    nlinarith [sq_nonneg (h - 121)]
  exact hb.trans (add_le_add_right hm ((8 * h + 33) ^ 2))

theorem trace_six_integral_cycle_count_lower (C : ℕ)
    (hC : (14586215 / 28 : ℝ) ≤ 12 * (C : ℝ)) : 43412 ≤ C := by
  by_contra hbad
  have hn : C ≤ 43411 := by omega
  have hr : (C : ℝ) ≤ 43411 := by exact_mod_cast hn
  nlinarith

theorem trace_six_equality_count_incompatible (hC : (14586215 / 28 : ℝ) ≤ 12 * 420) :
    False := by
  norm_num at hC

end TaskH.Six

#print axioms TaskH.Six.trace_six_scalar_lower_bound
#print axioms TaskH.Six.trace_six_integral_cycle_count_lower
#print axioms TaskH.Six.trace_six_equality_count_incompatible
