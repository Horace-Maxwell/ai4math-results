import Research.Backfill.Paper7.BMS32Polynomial
import Research.Backfill.Paper7.GraphPhiCharpoly

set_option autoImplicit false

namespace Paper7BMS32

/-- The exact frozen proposition, with all root multiplicities retained. -/
theorem check_BMSProposition32 : BackfillPaper7.Challenge.BMSProposition32 := by
  exact (Paper7GraphPhi.graphPhi_eq_charpoly
    (BackfillPaper7.Challenge.sunGraph 6 BackfillPaper7.Challenge.C61)).symm.trans
    c61_graphPhi

#print axioms Paper7BMS32.check_BMSProposition32

end Paper7BMS32
