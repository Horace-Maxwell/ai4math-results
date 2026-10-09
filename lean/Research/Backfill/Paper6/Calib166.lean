import Research.Backfill.Paper6.Calib166Part07

/-! Complete concrete witness of weight 166. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem weight_166 : BackfillPaper6.V3.IsWeight 6 12 166 :=
  concrete_witness masks166 166 masks166_bound masks166_degree calib166_prefix64

end Paper6Calib

#print axioms Paper6Calib.weight_166
