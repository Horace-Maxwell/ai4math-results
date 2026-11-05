import Mathlib

/-! Source-only factor-preserving cancellation. No polynomial expansion or
larger recursion/heartbeat budget is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open Polynomial

theorem eight_core_cancel_factor_ne_zero :
    (X^26*(X^2-1)^8 : Polynomial ℤ) ≠ 0 := by
  apply mul_ne_zero (pow_ne_zero _ X_ne_zero)
  exact pow_ne_zero _ ((monic_X_pow_sub_one (R := ℤ) (n := 2) (by decide)).ne_zero)
#print axioms Paper7EightCycle.eight_core_cancel_factor_ne_zero

theorem eight_core_power_shift (x u v w y z : Polynomial ℤ) :
    x^8*u*(x^24*v*w*y*z) = (x^26*u)*(x^6*v*w*y*z) := by
  calc
    x^8*u*(x^24*v*w*y*z) = (x^8*x^24)*u*(v*w*y*z) := by ac_rfl
    _ = (x^26*x^6)*u*(v*w*y*z) := by rw [← pow_add,← pow_add]
    _ = (x^26*u)*(x^6*v*w*y*z) := by ac_rfl
#print axioms Paper7EightCycle.eight_core_power_shift

theorem eight_core_cancel_shift (f : Polynomial ℤ)
    (h : X^26*((X^2-1)^8*f) =
      X^8*(X^2-1)^8*(X^24*(X^2-1)*(X^2-4)^2*(X^2-9)*(X^2-16))) :
    f = X^6*(X^2-1)*(X^2-4)^2*(X^2-9)*(X^2-16) := by
  apply mul_left_cancel₀ eight_core_cancel_factor_ne_zero
  calc
    (X^26*(X^2-1)^8)*f = X^26*((X^2-1)^8*f) := mul_assoc _ _ _
    _ = X^8*(X^2-1)^8*(X^24*(X^2-1)*(X^2-4)^2*(X^2-9)*(X^2-16)) := h
    _ = (X^26*(X^2-1)^8)*(X^6*(X^2-1)*(X^2-4)^2*(X^2-9)*(X^2-16)) :=
      eight_core_power_shift X ((X^2-1)^8) (X^2-1) ((X^2-4)^2) (X^2-9) (X^2-16)
#print axioms Paper7EightCycle.eight_core_cancel_shift

end Paper7EightCycle
