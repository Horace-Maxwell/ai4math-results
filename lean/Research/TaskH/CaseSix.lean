import Research.TaskH.Challenge

/-!
Task H: an additional partial target at k = 6. The original Challenge
and all-k Question2 remain unchanged. Definitions only, awaiting independent
statement review and a separate static freeze.
-/
set_option autoImplicit false

universe u

namespace TaskH.Challenge

/-- The original equality question at k = 6 over every finite vertex type. -/
def CaseSix : Prop := EqualityCase.{u} 6

/-- A concrete positive-example regression, with original edge-set counts. -/
def CompleteSevenCheck : Prop :=
  IsCriticalPlus 6 (⊤ : SimpleGraph (Fin 7)) ∧
    modCycleCount 6 (⊤ : SimpleGraph (Fin 7)) = 420 ∧ bound 6 = 420

end TaskH.Challenge
