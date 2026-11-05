import Research.Backfill.Paper7.SunPerron
import Research.Backfill.Paper7.Lemma24SmallEven

set_option autoImplicit false

namespace Paper7Admissible

/-- The entire exact frozen Lemma24, with its unrestricted original hypotheses. -/
theorem check_Lemma24 : BackfillPaper7.Challenge.Lemma24 := by
  intro b p q hb hp hG
  refine ⟨lemma24_perron b p q hb hp hG,
    (fun x hx => lemma24_large_multiplicity b p q hb x hx),
    (fun he => lemma24_counting_even b p q hb hG he),
    (fun ho => lemma24_counting_odd b p q hb hG ho),
    (fun he => lemma24_small_even_counts b p q hb hG he)⟩
#print axioms Paper7Admissible.check_Lemma24

end Paper7Admissible
