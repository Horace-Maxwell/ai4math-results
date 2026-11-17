import Research.TaskH.CaseSeven
import Research.TaskH.Seven.SevenCompleteCheck
import Research.TaskH.Seven.SevenLowerBound

/-! The exact frozen universal lower-bound contract, obtained from the
actual original good-cycle edge-set count. This is not the equality case. -/

set_option autoImplicit false
universe u
namespace TaskH

theorem lower_bound_seven : Challenge.LowerBoundSeven.{u} := by
  intro V _ G hcrit
  rw [Seven.bound_seven_eq_2880]
  exact Seven.critical_modCycleCount_ge_2880 hcrit

end TaskH

#print axioms TaskH.lower_bound_seven
