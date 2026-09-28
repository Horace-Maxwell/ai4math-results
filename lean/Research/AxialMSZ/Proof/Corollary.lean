import Research.AxialMSZ.Proof.ExS
import Research.AxialMSZ.Proof.ExE
import Research.AxialMSZ.Proof.ExD
import Research.AxialMSZ.Proof.SimpleIndecomposable

/-!
Assembly of all six conclusions of the frozen general corollary.
-/

set_option autoImplicit false

namespace CodexAxial
open AxialMSZ.Challenge


theorem check_Corollary : Corollary := by
  have hS : ExS.Statement := check_ExS_Statement
  have hD : ExD.Statement := check_ExD_Statement
  have hP : ExP.Statement := check_ExP_Statement
  have hF := check_Laws_facts
  refine ⟨check_not_MS_Conjecture_3_16, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hS.2.2.1
      (h ℚ (Fin 4 → ℚ) (JPlus (1/2 : ℚ)) ExS.μ ExS.X hF.1 hS.1 hS.2.2.2.1)
  · intro h
    exact hS.2.2.1
      (h ℚ (Fin 4 → ℚ) (JPlus (1/2 : ℚ)) ExS.μ ExS.X hF.1 hS.1
        (simple_not_decomposable hS.2.1))
  · intro h
    exact hS.2.2.1
      (h ℚ (Fin 4 → ℚ) (JPlus (1/2 : ℚ)) ExS.μ ExS.X hF.1 hS.1 hS.2.1)
  · intro h
    exact (h ℚ (Fin 5 → ℚ) (JMild (1/2 : ℚ)) ExD.μ ExD.X hF.2.2.1
      hD.1 (e 0) (by simp [ExD.X])) hD.2.1
  · refine ⟨ℚ, inferInstance, (Fin 2 → ℚ), inferInstance, inferInstance,
      FD3, ExP.μ, ExP.X, hF.2.2.2.1, hP.1, ?_⟩
    refine ⟨e 1, ?_, e 0, ?_, hP.2⟩ <;> simp [ExP.X]

#print axioms check_Corollary

end CodexAxial
