import Research.Backfill.Paper7.Corollary31Graph
import Research.Backfill.Paper7.KappaUnder200

/-! Exact original frozen contract, including the complete fourteen-entry list. -/
set_option autoImplicit false
namespace Paper7Corollary31

theorem check_Corollary31 : BackfillPaper7.Challenge.Corollary31 := by
  constructor
  · intro V _ _ G _ b hG hU ho
    exact corollary31_graph G b hG hU ho
  · exact kappa_under_200
#print axioms Paper7Corollary31.check_Corollary31

end Paper7Corollary31
