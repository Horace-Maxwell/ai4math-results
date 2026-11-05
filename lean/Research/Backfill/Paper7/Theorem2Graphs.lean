import Research.Backfill.Paper7.RepresentativeG13
import Research.Backfill.Paper7.RepresentativeG20a
import Research.Backfill.Paper7.RepresentativeG20b
import Research.Backfill.Paper7.GraphPhiCharpoly

set_option autoImplicit false

namespace Paper7ThreeRepresentatives

open BackfillPaper7.Challenge

theorem check_Theorem2Graphs : BackfillPaper7.Challenge.Theorem2Graphs := by
  exact ⟨g13_order, g20a_order, g20b_order,
    g13_pendant_positive, g20a_pendant_positive, g20b_pendant_positive,
    (Paper7GraphPhi.graphPhi_eq_charpoly (sunGraph 4 G13)).symm.trans g13_graphPhi,
    (Paper7GraphPhi.graphPhi_eq_charpoly (sunGraph 4 G20a)).symm.trans g20a_graphPhi,
    (Paper7GraphPhi.graphPhi_eq_charpoly (sunGraph 4 G20b)).symm.trans g20b_graphPhi⟩

#print axioms Paper7ThreeRepresentatives.check_Theorem2Graphs

end Paper7ThreeRepresentatives
