import Research.Backfill.Paper5.Proof.SignSmall
import Research.Backfill.Paper5.Proof.LiftRees

set_option autoImplicit false

namespace CodexPaper5
open BackfillPaper5

/-- Instantiate the explicit Rees lift with the actual sign section and even square bijection. -/
theorem check_Lemma42 : Challenge.Lemma42 := by
  intro r hr H _ _ P _ hq
  have hr2 : 2 ≤ r := by rcases hr with rfl | rfl <;> omega
  exact LiftRees.hasCM_lift P (SignSmall.rep r)
    (SignSmall.sgn_rep hr2)
    (fun a b ha hb hab => SignSmall.square_injective_even hr ha hb hab) hq

#print axioms CodexPaper5.check_Lemma42

end CodexPaper5
