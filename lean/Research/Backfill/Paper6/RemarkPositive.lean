import Research.Backfill.Paper6.Remark362

/-!
# All nineteen positive witnesses for the retained sparse-weight remark

The eighteen historical rows are combined with the actual analytic candidate
in Remark362.  The candidate dependency chain must still be compiled and
validated by Root.  This source does not claim any completed acceptance.
-/

set_option autoImplicit false

namespace Paper6RemarkWitnesses

open BackfillPaper6.V3

/-- All nineteen values on the frozen right-hand side have genuine witnesses. -/
theorem remark_positive (w : ℕ)
    (hw : w = 254 ∨ w = 314 ∨ w = 318 ∨
      (w % 4 = 2 ∧ 338 ≤ w ∧ w ≤ 398)) : w ∈ weightsLe5 := by
  by_cases h : w = 362
  · subst w
    exact weight_362
  · exact historical_positive w hw h

/-- The complete positive inclusion, with the original interval and congruence. -/
theorem remark_positive_subset :
    {w : ℕ | w = 254 ∨ w = 314 ∨ w = 318 ∨
      (w % 4 = 2 ∧ 338 ≤ w ∧ w ≤ 398)} ⊆
    {w | w ∈ weightsLe5 ∧ w % 4 = 2 ∧ 250 ≤ w ∧ w ≤ 400} := by
  intro w hw
  change w = 254 ∨ w = 314 ∨ w = 318 ∨
    (w % 4 = 2 ∧ 338 ≤ w ∧ w ≤ 398) at hw
  refine ⟨remark_positive w hw, ?_, ?_, ?_⟩ <;> omega

end Paper6RemarkWitnesses

#print axioms Paper6RemarkWitnesses.remark_positive
#print axioms Paper6RemarkWitnesses.remark_positive_subset
