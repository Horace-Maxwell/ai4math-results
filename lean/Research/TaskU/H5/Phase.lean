import Research.TaskU.H5.Challenge
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

namespace TaskU.H5.Phase
noncomputable section
open Finset
abbrev F := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The coefficient of π² in the ordinary line (j,1), reduced modulo five. -/
def moment (f : H → ℤ) (j : F) : F :=
  ∑ g, (f g : F) * ((g.a * j + g.b) * (g.a * j + g.b - 1) / 2)

theorem sum_moment (f : H → ℤ) : ∑ j, moment f j = 0 := by
  have h (a b : F) : ∑ j : F, ((a*j+b)*(a*j+b-1)/2) = 0 := by
    revert a b
    decide +kernel
  unfold moment
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, h, mul_zero, Finset.sum_const_zero]

theorem sum_phase (f : H → ℤ) (A : F) (k : F → F)
    (hk : ∀ j, k j = (2 / A) * moment f j - 1) : ∑ j, k j = 0 := by
  simp_rw [hk, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_moment, mul_zero]
  decide +kernel

private theorem char_sum (k : F → F) (s : Finset F) :
    ZMod.stdAddChar (∑ j ∈ s, k j) = ∏ j ∈ s, ZMod.stdAddChar (k j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, AddChar.map_add_eq_mul, ih]

/-- The four nonzero horizontal row products cancel in pairs. The phase is
transported through every cyclotomic embedding, indexed by r ≠ 0. -/
theorem row_trace (P : F → F → ℂ) (k : F → F) (hk : ∑ j, k j = 0)
    (hp : ∀ j r : F, r ≠ 0 →
      P ((-r)*j) (-r) = -(ZMod.stdAddChar (r*k j)) * P (r*j) r) :
    (∑ r : F, if r = 0 then 0 else ∏ t : F, P t r) = 0 := by
  let R (r : F) : ℂ := if r=0 then 0 else ∏ t : F, P t r
  have hrow (r : F) (hr : r ≠ 0) : (∏ t : F, P t (-r)) = -(∏ t : F, P t r) := by
    have reidx (v : F) (hv : v ≠ 0) :
        (∏ j : F, P (v*j) v) = ∏ t : F, P t v :=
      Equiv.prod_comp (Equiv.mulLeft₀ v hv) (fun t => P t v)
    rw [← reidx (-r) (neg_ne_zero.mpr hr), ← reidx r hr]
    simp_rw [hp _ _ hr, Finset.prod_mul_distrib]
    have hchar : (∏ j : F, ZMod.stdAddChar (r*k j)) = 1 := by
      rw [← char_sum, ← Finset.mul_sum, hk, mul_zero, AddChar.map_zero_eq_one]
    simp only [Finset.prod_neg, Finset.card_univ, ZMod.card, hchar]
    ring
  have hneg (r : F) : R (-r) = - R r := by
    by_cases hr : r=0
    · simp [R, hr]
    · simp [R, hr, hrow r hr]
  change ∑ r, R r = 0
  have hi : (∑ r : F, R (-r)) = ∑ r : F, R r :=
    Equiv.sum_comp (Equiv.neg F) R
  simp only [hneg, Finset.sum_neg_distrib] at hi
  linear_combination -hi / 2

end
end TaskU.H5.Phase
