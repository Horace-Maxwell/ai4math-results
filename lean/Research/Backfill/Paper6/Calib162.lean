import Research.Backfill.Paper6.Calib162Part07

/-! First calibration witness only: uncompiled candidate, not the complete Calib612 target. -/

set_option autoImplicit false

namespace Paper6Calib

theorem weight_162 : BackfillPaper6.V3.IsWeight 6 12 162 :=
  concrete_witness masks162 162 masks162_bound masks162_degree calib162_prefix64


end Paper6Calib

#print axioms Paper6Calib.weight_162
