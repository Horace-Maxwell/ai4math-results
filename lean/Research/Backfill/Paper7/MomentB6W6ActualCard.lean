import Research.Backfill.Paper7.MomentB6SixTripleConvolutionV2

/-! NEW uncompiled candidate. Unit 1: identify the existing signed W6
formula with the actual bounded-q fibre, using successful actual858.
No numerical value, enumeration, resource override or new premise. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

theorem labelledSixQWeight_eq_actual_card (z : Fin 6 → ℕ) (Q : ℕ) :
    labelledSixQWeight z Q =
      (Nat.card {q : (i : Fin 6) → Fin (z i + 1) // ∑ i, (q i).val = Q} : ℤ) := by
  simpa only [labelledSixQWeight, labelledPositiveFiveBinomial] using
    (bounded_q_six_inclusion_exclusion_W6_form z Q).symm
#print axioms Paper7MomentCounts.labelledSixQWeight_eq_actual_card

end Paper7MomentCounts
