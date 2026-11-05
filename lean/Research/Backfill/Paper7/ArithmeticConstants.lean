import Research.Backfill.Paper7.ChallengeV3

/-! The complete frozen ArithmeticConstants contract: twelve closed finite
arithmetic facts. The decision procedure below is reduced by the Lean kernel.
This source candidate has not been compiled by its author. -/
set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper7Arithmetic

theorem check_ArithmeticConstants : BackfillPaper7.Challenge.ArithmeticConstants := by
  unfold BackfillPaper7.Challenge.ArithmeticConstants
  decide +kernel
#print axioms Paper7Arithmetic.check_ArithmeticConstants

end Paper7Arithmetic
