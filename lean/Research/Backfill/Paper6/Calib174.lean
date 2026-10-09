import Research.Backfill.Paper6.Calib174Part07

/-! Complete concrete witness of weight 174. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem weight_174 : BackfillPaper6.V3.IsWeight 6 12 174 :=
  concrete_witness masks174 174 masks174_bound masks174_degree calib174_prefix64

end Paper6Calib

#print axioms Paper6Calib.weight_174
