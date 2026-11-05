import Research.Backfill.Paper7.Lemma51Ordinary
import Research.Backfill.Paper7.ExceptionalThresholdBounds

set_option autoImplicit false

namespace Paper7Comparison

/-- Exactly the complete frozen contract: both ordinary and exceptional branches,
with every original strict/non-strict inequality and no additional premise. -/
theorem check_Lemma51 : BackfillPaper7.Challenge.Lemma51 := by
  intro b p q hb
  constructor
  · intro m t hm ht
    exact lemma51_ordinary b p q hb m t hm ht
  · intro Y t hY ht
    exact Paper7Exceptional.lemma51_exceptional b p q hb Y t hY ht
#print axioms Paper7Comparison.check_Lemma51

end Paper7Comparison
