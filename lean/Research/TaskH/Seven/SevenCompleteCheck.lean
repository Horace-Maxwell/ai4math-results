import Research.TaskH.CaseSeven
import Research.TaskH.CompleteCritical
import Research.TaskH.Seven.SevenCompleteWords

/-! Original positive complete-graph contract and neighboring-order negative
checks. These do not assume, or assert a proof of, MainSeven or CaseSeven. -/

set_option autoImplicit false

namespace TaskH.Seven

open SimpleGraph Challenge

theorem completeEight_isCriticalPlus : IsCriticalPlus 7 (⊤ : SimpleGraph (Fin 8)) :=
  TaskH.complete_isCriticalPlus 7

theorem bound_seven_eq_2880 : bound 7 = 2880 := by
  norm_num [bound]

theorem completeEight_check : Challenge.CompleteEightCheck := by
  exact ⟨completeEight_isCriticalPlus, completeEight_modCycleCount, bound_seven_eq_2880⟩

theorem complete_seven_is_not_eight_critical :
    ¬ IsCriticalPlus 7 (⊤ : SimpleGraph (Fin 7)) := by
  intro h
  have hc := h.1
  simp only [chromaticNumber_top, Fintype.card_fin] at hc
  norm_num at hc

theorem complete_nine_is_not_eight_critical :
    ¬ IsCriticalPlus 7 (⊤ : SimpleGraph (Fin 9)) := by
  intro h
  have hc := h.1
  simp only [chromaticNumber_top, Fintype.card_fin] at hc
  norm_num at hc

end TaskH.Seven

#print axioms TaskH.Seven.completeEight_isCriticalPlus
#print axioms TaskH.Seven.bound_seven_eq_2880
#print axioms TaskH.Seven.completeEight_check
#print axioms TaskH.Seven.complete_seven_is_not_eight_critical
#print axioms TaskH.Seven.complete_nine_is_not_eight_critical
