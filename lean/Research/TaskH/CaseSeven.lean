import Research.TaskH.Challenge

/-!
Task H, the original question specialized to k = 7.
Definitions only, pending independent statement review and SHA freeze.
The original Challenge and all-k Question2 remain unchanged.
-/

set_option autoImplicit false

universe u

namespace TaskH.Challenge

/-- The original equality case on every finite vertex type. -/
def CaseSeven : Prop := EqualityCase.{u} 7

/-- The original lower bound, to be proved as part of the counting context. -/
def LowerBoundSeven : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
    IsCriticalPlus 7 G → bound 7 ≤ modCycleCount 7 G

/-- The complete graph positive regression with the original cycle count. -/
def CompleteEightCheck : Prop :=
  IsCriticalPlus 7 (⊤ : SimpleGraph (Fin 8)) ∧
    modCycleCount 7 (⊤ : SimpleGraph (Fin 8)) = 2880 ∧ bound 7 = 2880

end TaskH.Challenge
