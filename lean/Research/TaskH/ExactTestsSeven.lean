import Research.TaskH.MainSeven

/-! Exact original-head regressions for the frozen k=7 partial target.
These source candidates receive credit only after whole-source verification. -/

set_option autoImplicit false

universe u

namespace TaskH.TestsSeven

open Challenge SimpleGraph

theorem exact_frozen_case_seven : CaseSeven.{u} := TaskH.case_seven

theorem original_head (V : Type u) [Fintype V] (G : SimpleGraph V)
    (hcrit : IsCriticalPlus 7 G) (hcount : modCycleCount 7 G = bound 7) :
    IsCompleteOfOrder G 8 := TaskH.case_seven V G hcrit hcount

theorem original_complete_example : CompleteEightCheck := TaskH.Seven.completeEight_check

theorem complete_seven_is_not_eight_critical :
    ¬ IsCriticalPlus 7 (⊤ : SimpleGraph (Fin 7)) :=
  TaskH.Seven.complete_seven_is_not_eight_critical

theorem complete_nine_is_not_eight_critical :
    ¬ IsCriticalPlus 7 (⊤ : SimpleGraph (Fin 9)) :=
  TaskH.Seven.complete_nine_is_not_eight_critical

end TaskH.TestsSeven

#print axioms TaskH.TestsSeven.exact_frozen_case_seven
#print axioms TaskH.TestsSeven.original_head
#print axioms TaskH.TestsSeven.original_complete_example
#print axioms TaskH.TestsSeven.complete_seven_is_not_eight_critical
#print axioms TaskH.TestsSeven.complete_nine_is_not_eight_critical
