import Research.TaskH.MainFive

/-! Exact-head and concrete-example regressions for the frozen k=5 target.
The criticality premise still quantifies over every proper subgraph. -/

set_option autoImplicit false

universe u

namespace TaskH.TestsFive

open Challenge SimpleGraph

theorem exact_frozen_case_five : CaseFive.{u} := TaskH.case_five

theorem original_head (V : Type u) [Fintype V] (G : SimpleGraph V)
    (hcrit : IsCriticalPlus 5 G) (hcount : modCycleCount 5 G = bound 5) :
    IsCompleteOfOrder G 6 := TaskH.case_five V G hcrit hcount

theorem original_complete_example : CompleteSixCheck := TaskH.Five.completeSix_check

theorem complete_five_is_not_six_critical :
    ¬ IsCriticalPlus 5 (⊤ : SimpleGraph (Fin 5)) := by
  intro h
  have hc := h.1
  simp only [chromaticNumber_top, Fintype.card_fin] at hc
  norm_num at hc

theorem complete_seven_is_not_six_critical :
    ¬ IsCriticalPlus 5 (⊤ : SimpleGraph (Fin 7)) := by
  intro h
  have hc := h.1
  simp only [chromaticNumber_top, Fintype.card_fin] at hc
  norm_num at hc

end TaskH.TestsFive

#print axioms TaskH.TestsFive.exact_frozen_case_five
#print axioms TaskH.TestsFive.original_head
#print axioms TaskH.TestsFive.original_complete_example
#print axioms TaskH.TestsFive.complete_five_is_not_six_critical
#print axioms TaskH.TestsFive.complete_seven_is_not_six_critical
