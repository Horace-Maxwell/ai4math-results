import Research.AxialMSZ.Challenge
import Research.AxialMSZ.SupplementDChallenge

/-!
# Comparator challenge for Paper 9 (axial algebras)

For the comparator (https://github.com/leanprover/comparator). Every theorem below
states, with a `sorry` proof, exactly the type of the theorem of the same name in
`Research/AxialMSZ/Check.lean`, which is the solution module. The statements refer only
to the frozen statement files `Research/AxialMSZ/Challenge.lean` (SHA-256
`0d88e732…3ee1`) and `Research/AxialMSZ/SupplementDChallenge.lean` (SHA-256
`afd751c0…c9175`), which import only Mathlib.

The `sorry`s are intentional: comparator checks that the solution proves the same
statements, using only the permitted axioms, and replays it in the Lean kernel and in
the independent kernel nanoda. This module is not imported by `Research.lean`.
-/

set_option autoImplicit false

namespace AxialMSZ.Check

theorem check_Laws_facts : AxialMSZ.Challenge.Laws_facts := sorry

theorem check_ExS_Statement : AxialMSZ.Challenge.ExS.Statement := sorry

theorem check_ExE_Statement : AxialMSZ.Challenge.ExE.Statement := sorry

theorem check_ExD_Statement : AxialMSZ.Challenge.ExD.Statement := sorry

theorem check_ExP_Statement : AxialMSZ.Challenge.ExP.Statement := sorry

theorem check_TheoremA : AxialMSZ.Challenge.TheoremA := sorry

theorem check_TheoremB : AxialMSZ.Challenge.TheoremB := sorry

theorem check_TheoremC : AxialMSZ.Challenge.TheoremC := sorry

theorem check_RemarkP : AxialMSZ.Challenge.RemarkP := sorry

theorem check_Corollary : AxialMSZ.Challenge.Corollary := sorry

theorem check_not_MS_Conjecture_3_16 : ¬ AxialMSZ.Challenge.MS_Conjecture_3_16 := sorry

theorem check_not_FinestSumDecomposition_connected : ¬ AxialMSZ.Challenge.FinestSumDecomposition_connected := sorry

theorem check_not_Indecomposable_connected : ¬ AxialMSZ.Challenge.Indecomposable_connected := sorry

theorem check_not_Simple_connected : ¬ AxialMSZ.Challenge.Simple_connected := sorry

theorem check_Dominance_nonsymmetric : AxialMSZ.Challenge.Dominance_nonsymmetric := sorry

theorem check_ExD_axes_in_block : CodexAxial.SupplementChallenge.ExD_axes_in_block := sorry

theorem check_ExD_block_not_axial_on_contained_axes : CodexAxial.SupplementChallenge.ExD_block_not_axial_on_contained_axes := sorry

end AxialMSZ.Check
