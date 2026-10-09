import Research.Backfill.Paper6.Calib162
import Research.Backfill.Paper6.Calib166
import Research.Backfill.Paper6.Calib170
import Research.Backfill.Paper6.Calib174

/-! The exact frozen four-member Calib612 target. Candidate only; compilation and independent acceptance pending. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper6Calib

theorem check_Calib612 : BackfillPaper6.V3.Calib612 := by
  intro w hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact weight_162
  · exact weight_166
  · exact weight_170
  · exact weight_174

end Paper6Calib

#print axioms Paper6Calib.check_Calib612
