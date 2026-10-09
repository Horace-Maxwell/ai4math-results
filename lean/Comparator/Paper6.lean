import Research.Backfill.Paper6.ChallengeV3
import Research.Backfill.Paper6.BridgeChallenge

/-!
# Comparator challenge for Paper 6, version 2 (fourteen new weights of the Reed–Muller code RM(7,14))

For the comparator (https://github.com/leanprover/comparator). Every theorem below
states, with a `sorry` proof, exactly the type of the theorem of the same name in
`Research/Backfill/Paper6/CheckPaper6.lean`, which is the solution module. The statements
refer only to the frozen statement files `Research/Backfill/Paper6/ChallengeV3.lean`
(SHA-256 `83ea2291…b6d78`, which imports only Mathlib) and
`Research/Backfill/Paper6/BridgeChallenge.lean`, which imports the statement file and the
published module `Research/RM714Weights.lean` of version 1, whose weight predicate the
statement `Sec7Bridge` compares with the one defined here.

The `sorry`s are intentional: comparator checks that the solution proves the same
statements, using only the permitted axioms, and replays it in the Lean kernel and in
the independent kernel nanoda. This module is not imported by `Research.lean`.
-/

set_option autoImplicit false

namespace Paper6FinalPackageV4

theorem check_P1 : BackfillPaper6.V3.P1 := sorry

theorem check_P2 : BackfillPaper6.V3.P2 := sorry

theorem check_P3_minWeight : BackfillPaper6.V3.P3_minWeight := sorry

theorem check_Lem21 : BackfillPaper6.V3.Lem21 := sorry

theorem check_Lem21_venn : BackfillPaper6.V3.Lem21_venn := sorry

theorem check_Lem22 : BackfillPaper6.V3.Lem22 := sorry

theorem check_ThmA : BackfillPaper6.V3.ThmA := sorry

theorem check_Table1 : BackfillPaper6.V3.Table1 := sorry

theorem check_Rem31 : BackfillPaper6.V3.Rem31 := sorry

theorem check_ThmB_witnesses : BackfillPaper6.V3.ThmB_witnesses := sorry

theorem check_S0_card : BackfillPaper6.V3.S0_card := sorry

theorem check_CarletEquiv : BackfillPaper6.V3.CarletEquiv := sorry

theorem check_IntroMU : BackfillPaper6.V3.IntroMU := sorry

theorem check_LAProp4 : BackfillPaper6.V3.LAProp4 := sorry

theorem check_LWConstrInRM : BackfillPaper6.V3.LWConstrInRM := sorry

theorem check_LWConj2_gives : BackfillPaper6.V3.LWConj2_gives := sorry

theorem check_ThmC_literal : BackfillPaper6.V3.ThmC_literal := sorry

theorem check_Sec4Concat : BackfillPaper6.V3.Sec4Concat := sorry

theorem check_FactStar : BackfillPaper6.V3.FactStar := sorry

theorem check_TransversalDim : BackfillPaper6.V3.TransversalDim := sorry

theorem check_PropD : BackfillPaper6.V3.PropD := sorry

theorem check_RemD162 : BackfillPaper6.V3.RemD162 := sorry

theorem check_PropE : BackfillPaper6.V3.PropE := sorry

theorem check_PropE_remark_2mod4 : BackfillPaper6.V3.PropE_remark_2mod4 := sorry

theorem check_Lem51 : BackfillPaper6.V3.Lem51 := sorry

theorem check_PropF : BackfillPaper6.V3.PropF := sorry

theorem check_MinDist : BackfillPaper6.V3.MinDist := sorry

theorem check_FlatBasics : BackfillPaper6.V3.FlatBasics := sorry

theorem check_AffineInvariance : BackfillPaper6.V3.AffineInvariance := sorry

theorem check_Cat4Weight : BackfillPaper6.V3.Cat4Weight := sorry

theorem check_Calib612 : BackfillPaper6.V3.Calib612 := sorry

theorem check_S0_eq_LA : BackfillPaper6.V3.S0_eq_LA := sorry

theorem check_ThmA_mathlib : BackfillPaper6.V3.ThmA_mathlib := sorry

theorem check_PropE_mathlib : BackfillPaper6.V3.PropE_mathlib := sorry

theorem check_Sec7Bridge : BackfillPaper6.V3.Sec7Bridge := sorry

end Paper6FinalPackageV4
