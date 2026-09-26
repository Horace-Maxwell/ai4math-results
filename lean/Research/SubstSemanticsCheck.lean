import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic
open PowerSeries
/-! Statement-fidelity check for `Oeis389472Mod3.integer_conjecture`:
`A.subst h` denotes A(h), i.e. h is substituted INTO A.
Were it h(A), the left side below would equal (X + X^2) evaluated at X^2,
namely X^2 + X^4, which differs from (X + X^2)^2 in the X^3 coefficient. -/
example : (X ^ 2 : PowerSeries ℤ).subst (X + X ^ 2 : PowerSeries ℤ) = (X + X ^ 2) ^ 2 := by
  have ha : HasSubst (X + X ^ 2 : PowerSeries ℤ) := HasSubst.of_constantCoeff_zero' (by simp)
  rw [← coe_substAlgHom ha, map_pow, coe_substAlgHom ha, subst_X ha]
