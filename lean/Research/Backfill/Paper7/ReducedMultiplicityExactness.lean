import Research.Backfill.Paper7.ZeroMultiplicity
import Research.Backfill.Paper7.SignMultiplicity

set_option autoImplicit false

namespace Paper7Reduced

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem check_ReducedMultiplicityExactness :
    BackfillPaper7.Challenge.Legacy.Algebra.ReducedMultiplicityExactness := by
  intro b p q hb
  exact ⟨freeP_add_card b p, freeQ_add_card b q,
    freeP_eq_sub b p, freeQ_eq_sub b q,
    ordinary_reduced_multiplicity b p q hb,
    zero_reduced_multiplicity b p q hb,
    sign_reduced_multiplicity b p q hb⟩

#print axioms Paper7Reduced.check_ReducedMultiplicityExactness

end Paper7Reduced
