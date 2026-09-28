import Research.AxialMSZ.Proof.ExSGraph
import Research.AxialMSZ.Proof.ExSDecomp
import Research.AxialMSZ.Proof.Laws

set_option autoImplicit false
namespace CodexAxial
open AxialMSZ.Challenge

theorem check_TheoremA : AxialMSZ.Challenge.TheoremA :=
  ⟨SimpleExample.axial, SimpleExample.simple, SimpleExample.disconnected,
    simple_onlyTrivialSumDecompositions SimpleExample.commutative SimpleExample.simple,
    SimpleExample.components_do_not_annihilate⟩

theorem check_ExS_Statement : AxialMSZ.Challenge.ExS.Statement := check_TheoremA

/-- The full universal general-fusion-law conjecture is refuted by the frozen example S. -/
theorem check_not_MS_Conjecture_3_16 : ¬ AxialMSZ.Challenge.MS_Conjecture_3_16 := by
  intro h
  exact SimpleExample.components_do_not_annihilate
    (h ℚ (Fin 4 → ℚ) (JPlus (1/2 : ℚ)) ExS.μ ExS.X
      check_Laws_facts.1 SimpleExample.axial)

#print axioms check_TheoremA
#print axioms check_ExS_Statement
#print axioms check_not_MS_Conjecture_3_16
end CodexAxial
