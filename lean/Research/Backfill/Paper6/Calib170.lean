import Research.Backfill.Paper6.Calib170Part07

/-! Complete concrete witness of weight 170. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem weight_170 : BackfillPaper6.V3.IsWeight 6 12 170 :=
  concrete_witness masks170 170 masks170_bound masks170_degree calib170_prefix64

end Paper6Calib

#print axioms Paper6Calib.weight_170
