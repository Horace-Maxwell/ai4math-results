import Research.TaskH.CompleteCritical
import Research.TaskH.CycleFourWitness

set_option autoImplicit false

namespace TaskH

theorem completeFive_check : Challenge.CompleteFiveCheck := by
  refine ⟨complete_isCriticalPlus 4, FourCount.completeFive_modCycleCount, ?_⟩
  decide +kernel

#print axioms completeFive_check

end TaskH
