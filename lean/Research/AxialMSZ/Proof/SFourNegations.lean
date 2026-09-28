import Research.AxialMSZ.Proof.ExS
import Research.AxialMSZ.Proof.SimpleIndecomposable

/-! Four separate refutations obtained from TheoremA and Laws_facts.
This module does not import ExE, ExD, or the combined Corollary.
-/

set_option autoImplicit false

namespace CodexAxial.FromS
open AxialMSZ.Challenge

theorem check_not_MS_Conjecture_3_16 : ¬ MS_Conjecture_3_16 := by
  have hS : ExS.Statement := check_TheoremA
  intro h
  exact hS.2.2.2.2
    (h ℚ (Fin 4 → ℚ) (JPlus (1/2 : ℚ)) ExS.μ ExS.X check_Laws_facts.1 hS.1)

theorem check_not_FinestSumDecomposition_connected : ¬ FinestSumDecomposition_connected := by
  have hS : ExS.Statement := check_TheoremA
  intro h
  exact hS.2.2.1
    (h ℚ (Fin 4 → ℚ) (JPlus (1/2 : ℚ)) ExS.μ ExS.X check_Laws_facts.1 hS.1
      hS.2.2.2.1)

theorem check_not_Indecomposable_connected : ¬ Indecomposable_connected := by
  have hS : ExS.Statement := check_TheoremA
  intro h
  exact hS.2.2.1
    (h ℚ (Fin 4 → ℚ) (JPlus (1/2 : ℚ)) ExS.μ ExS.X check_Laws_facts.1 hS.1
      (simple_not_decomposable hS.2.1))

theorem check_not_Simple_connected : ¬ Simple_connected := by
  have hS : ExS.Statement := check_TheoremA
  intro h
  exact hS.2.2.1
    (h ℚ (Fin 4 → ℚ) (JPlus (1/2 : ℚ)) ExS.μ ExS.X check_Laws_facts.1 hS.1 hS.2.1)

#print axioms check_not_MS_Conjecture_3_16
#print axioms check_not_FinestSumDecomposition_connected
#print axioms check_not_Indecomposable_connected
#print axioms check_not_Simple_connected

end CodexAxial.FromS
