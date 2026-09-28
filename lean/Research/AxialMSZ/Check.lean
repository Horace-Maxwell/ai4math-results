import Research.AxialMSZ.Proof.Corollary
import Research.AxialMSZ.Proof.SFourNegations
import Research.AxialMSZ.Proof.PConsequence
import Research.AxialMSZ.Proof.ExDSupplement

set_option autoImplicit false

namespace AxialMSZ.Check

theorem check_Laws_facts : AxialMSZ.Challenge.Laws_facts :=
  CodexAxial.check_Laws_facts

theorem check_ExS_Statement : AxialMSZ.Challenge.ExS.Statement :=
  CodexAxial.check_ExS_Statement

theorem check_ExE_Statement : AxialMSZ.Challenge.ExE.Statement :=
  CodexAxial.check_ExE_Statement

theorem check_ExD_Statement : AxialMSZ.Challenge.ExD.Statement :=
  CodexAxial.check_ExD_Statement

theorem check_ExP_Statement : AxialMSZ.Challenge.ExP.Statement :=
  CodexAxial.check_ExP_Statement

theorem check_TheoremA : AxialMSZ.Challenge.TheoremA :=
  CodexAxial.check_TheoremA

theorem check_TheoremB : AxialMSZ.Challenge.TheoremB :=
  CodexAxial.check_TheoremB

theorem check_TheoremC : AxialMSZ.Challenge.TheoremC :=
  CodexAxial.check_TheoremC

theorem check_RemarkP : AxialMSZ.Challenge.RemarkP :=
  CodexAxial.check_RemarkP

theorem check_Corollary : AxialMSZ.Challenge.Corollary :=
  CodexAxial.check_Corollary

theorem check_not_MS_Conjecture_3_16 : ¬ AxialMSZ.Challenge.MS_Conjecture_3_16 :=
  CodexAxial.FromS.check_not_MS_Conjecture_3_16

theorem check_not_FinestSumDecomposition_connected : ¬ AxialMSZ.Challenge.FinestSumDecomposition_connected :=
  CodexAxial.FromS.check_not_FinestSumDecomposition_connected

theorem check_not_Indecomposable_connected : ¬ AxialMSZ.Challenge.Indecomposable_connected :=
  CodexAxial.FromS.check_not_Indecomposable_connected

theorem check_not_Simple_connected : ¬ AxialMSZ.Challenge.Simple_connected :=
  CodexAxial.FromS.check_not_Simple_connected

theorem check_Dominance_nonsymmetric : AxialMSZ.Challenge.Dominance_nonsymmetric :=
  CodexAxial.FromP.check_Dominance_nonsymmetric

theorem check_ExD_axes_in_block : CodexAxial.SupplementChallenge.ExD_axes_in_block :=
  CodexAxial.check_ExD_axes_in_block

theorem check_ExD_block_not_axial_on_contained_axes : CodexAxial.SupplementChallenge.ExD_block_not_axial_on_contained_axes :=
  CodexAxial.check_ExD_block_not_axial_on_contained_axes

#print axioms check_Laws_facts
#print axioms check_ExS_Statement
#print axioms check_ExE_Statement
#print axioms check_ExD_Statement
#print axioms check_ExP_Statement
#print axioms check_TheoremA
#print axioms check_TheoremB
#print axioms check_TheoremC
#print axioms check_RemarkP
#print axioms check_Corollary
#print axioms check_not_MS_Conjecture_3_16
#print axioms check_not_FinestSumDecomposition_connected
#print axioms check_not_Indecomposable_connected
#print axioms check_not_Simple_connected
#print axioms check_Dominance_nonsymmetric
#print axioms check_ExD_axes_in_block
#print axioms check_ExD_block_not_axial_on_contained_axes

end AxialMSZ.Check
