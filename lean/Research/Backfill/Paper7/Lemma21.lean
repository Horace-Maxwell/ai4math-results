import Research.Backfill.Paper7.Lemma21Ordinary
import Research.Backfill.Paper7.Lemma21Exceptional

/-! Source-only assembly of the complete original frozen Lemma21. -/
set_option autoImplicit false
namespace Paper7Lemma21

theorem check_Lemma21 : BackfillPaper7.Challenge.Lemma21 := by
  intro b p q hb
  have ho := lemma21_ordinary b p q hb
  have he := lemma21_exceptional b p q hb
  exact ⟨ho.1, ho.2, he.1, he.2⟩
#print axioms Paper7Lemma21.check_Lemma21

end Paper7Lemma21
