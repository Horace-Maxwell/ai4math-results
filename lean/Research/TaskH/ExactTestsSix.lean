import Research.TaskH.MainSix

/-! Original graph-criticality and exact-head regressions for the k=6 partial target. -/

set_option autoImplicit false

universe u

namespace TaskH.TestsSix

open Challenge SimpleGraph

theorem exact_frozen_case_six : CaseSix.{u} := TaskH.case_six

theorem original_head (V : Type u) [Fintype V] (G : SimpleGraph V)
    (hcrit : IsCriticalPlus 6 G) (hcount : modCycleCount 6 G = bound 6) :
    IsCompleteOfOrder G 7 := TaskH.case_six V G hcrit hcount

theorem original_complete_example : CompleteSevenCheck := TaskH.Six.completeSeven_check

theorem complete_six_is_not_seven_critical :
    ¬ IsCriticalPlus 6 (⊤ : SimpleGraph (Fin 6)) := by
  intro h
  have hc := h.1
  simp only [chromaticNumber_top, Fintype.card_fin] at hc
  norm_num at hc

theorem complete_eight_is_not_seven_critical :
    ¬ IsCriticalPlus 6 (⊤ : SimpleGraph (Fin 8)) := by
  intro h
  have hc := h.1
  simp only [chromaticNumber_top, Fintype.card_fin] at hc
  norm_num at hc

end TaskH.TestsSix

#print axioms TaskH.TestsSix.exact_frozen_case_six
#print axioms TaskH.TestsSix.original_head
#print axioms TaskH.TestsSix.original_complete_example
#print axioms TaskH.TestsSix.complete_six_is_not_seven_critical
#print axioms TaskH.TestsSix.complete_eight_is_not_seven_critical
