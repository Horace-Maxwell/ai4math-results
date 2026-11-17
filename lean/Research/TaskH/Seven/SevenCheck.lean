import Research.TaskH.ExactTestsSeven
import Research.TaskH.Seven.SevenOriginalLowerBound

/-! The three frozen k=7 contracts, without changing the all-k question. -/

set_option autoImplicit false

universe u

namespace TaskH.CheckSeven

theorem check_case_seven : Challenge.CaseSeven.{u} := TaskH.case_seven

theorem check_lower_bound_seven : Challenge.LowerBoundSeven.{u} := TaskH.lower_bound_seven

theorem check_complete_eight : Challenge.CompleteEightCheck := TaskH.Seven.completeEight_check

end TaskH.CheckSeven

#print axioms TaskH.CheckSeven.check_case_seven
#print axioms TaskH.CheckSeven.check_lower_bound_seven
#print axioms TaskH.CheckSeven.check_complete_eight
