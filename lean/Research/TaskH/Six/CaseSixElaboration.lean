import Research.TaskH.CaseSix

/-! Elaboration checks for the independently frozen k=6 partial definitions. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge

theorem caseSix_original_definition :
    CaseSix.{u} = EqualityCase.{u} 6 := rfl

theorem completeSeven_original_definition :
    CompleteSevenCheck =
      (IsCriticalPlus 6 (⊤ : SimpleGraph (Fin 7)) ∧
        modCycleCount 6 (⊤ : SimpleGraph (Fin 7)) = 420 ∧ bound 6 = 420) := rfl

end TaskH.Six

#print axioms TaskH.Challenge.CaseSix
#print axioms TaskH.Challenge.CompleteSevenCheck
#print axioms TaskH.Six.caseSix_original_definition
#print axioms TaskH.Six.completeSeven_original_definition
