import Research.TaskH.MainFour

/-!
Exact original-head and concrete-example regressions. In particular, the
criticality premise retains the true chromatic number and all proper
subgraphs. No finite-order or maximum-cycle-length premise is added.
-/

set_option autoImplicit false

universe u

namespace TaskH.Tests

open Challenge SimpleGraph

theorem exact_frozen_case_four : CaseFour.{u} := TaskH.case_four

theorem original_head (V : Type u) [Fintype V] (G : SimpleGraph V)
    (hcrit : IsCriticalPlus 4 G) (hcount : modCycleCount 4 G = bound 4) :
    IsCompleteOfOrder G 5 := TaskH.case_four V G hcrit hcount

theorem original_complete_example : CompleteFiveCheck := TaskH.completeFive_check

theorem complete_four_is_not_five_critical :
    ¬ IsCriticalPlus 4 (⊤ : SimpleGraph (Fin 4)) := by
  intro h
  have hc := h.1
  simp only [chromaticNumber_top, Fintype.card_fin] at hc
  norm_num at hc

theorem complete_six_is_not_five_critical :
    ¬ IsCriticalPlus 4 (⊤ : SimpleGraph (Fin 6)) := by
  intro h
  have hc := h.1
  simp only [chromaticNumber_top, Fintype.card_fin] at hc
  norm_num at hc

end TaskH.Tests

#print axioms TaskH.Tests.exact_frozen_case_four
#print axioms TaskH.Tests.original_head
#print axioms TaskH.Tests.original_complete_example
#print axioms TaskH.Tests.complete_four_is_not_five_critical
#print axioms TaskH.Tests.complete_six_is_not_five_critical
