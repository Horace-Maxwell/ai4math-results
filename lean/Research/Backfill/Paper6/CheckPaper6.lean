import Research.Backfill.Paper6.ChallengeV3Tests
import Research.Backfill.Paper6.BridgeChallenge
import Research.Backfill.Paper6.P1
import Research.Backfill.Paper6.P2
import Research.Backfill.Paper6.P3
import Research.Backfill.Paper6.InclusionExclusion
import Research.Backfill.Paper6.InclusionExclusionVenn
import Research.Backfill.Paper6.Lem22
import Research.Backfill.Paper6.CheckFirstBatch
import Research.Backfill.Paper6.Table1
import Research.Backfill.Paper6.Rem31
import Research.Backfill.Paper6.S0Witnesses
import Research.Backfill.Paper6.SpectralConsequences
import Research.Backfill.Paper6.LouWang
import Research.Backfill.Paper6.LiteralLouWang
import Research.Backfill.Paper6.FactStar
import Research.Backfill.Paper6.TransversalDim
import Research.Backfill.Paper6.PropD
import Research.Backfill.Paper6.Remark162
import Research.Backfill.Paper6.PropEExclusion
import Research.Backfill.Paper6.PropERemark
import Research.Backfill.Paper6.Lem51
import Research.Backfill.Paper6.PropF
import Research.Backfill.Paper6.MinDist
import Research.Backfill.Paper6.FlatBasics
import Research.Backfill.Paper6.AffineInvariance
import Research.Backfill.Paper6.Cat4Weight
import Research.Backfill.Paper6.Calib612
import Research.Backfill.Paper6.ThmAMathlibV4
import Research.Backfill.Paper6.PropEMathlibV4
import Research.Backfill.Paper6.Sec7Bridge

/-!
# Paper 6 V4: checks for all 35 retained mathematical contracts

The isolated predecessor package passed complete validation and independent review.
This publication-layout copy preserves every declaration and namespace; only local
import paths and this documentation comment are updated. The new layout and its
unchanged published legacy dependency require a separate validation receipt.

Resolve all local Paper6 imports in Research.Backfill.Paper6. The 98 frozen tests,
including the vennVectors test, are retained. Cancelled count modules are excluded.
-/

set_option autoImplicit false

namespace Paper6FinalPackageV4

theorem check_P1 : BackfillPaper6.V3.P1 := Paper6Parity.check_P1
theorem check_P2 : BackfillPaper6.V3.P2 := Paper6Divisibility.check_P2
theorem check_P3_minWeight : BackfillPaper6.V3.P3_minWeight :=
  Paper6MinimumStructure.check_P3_minWeight
theorem check_Lem21 : BackfillPaper6.V3.Lem21 := Paper6InclusionExclusion.check_Lem21
theorem check_Lem21_venn : BackfillPaper6.V3.Lem21_venn :=
  Paper6InclusionExclusionVenn.check_Lem21_venn
theorem check_Lem22 : BackfillPaper6.V3.Lem22 := Paper6HalfDecomposition.check_Lem22
theorem check_ThmA : BackfillPaper6.V3.ThmA := Paper6FirstBatch.check_ThmA
theorem check_Table1 : BackfillPaper6.V3.Table1 := Paper6TableOne.check_Table1
theorem check_Rem31 : BackfillPaper6.V3.Rem31 := Paper6DirectSums.check_Rem31
theorem check_ThmB_witnesses : BackfillPaper6.V3.ThmB_witnesses :=
  Paper6S0Witnesses.check_ThmB_witnesses
theorem check_S0_card : BackfillPaper6.V3.S0_card := Paper6FirstBatch.check_S0_card
theorem check_CarletEquiv : BackfillPaper6.V3.CarletEquiv :=
  Paper6SpectralConsequences.check_CarletEquiv
theorem check_IntroMU : BackfillPaper6.V3.IntroMU := Paper6FirstBatch.check_IntroMU
theorem check_LAProp4 : BackfillPaper6.V3.LAProp4 := Paper6SpectralConsequences.check_LAProp4
theorem check_LWConstrInRM : BackfillPaper6.V3.LWConstrInRM :=
  Paper6LouWang.check_LWConstrInRM
theorem check_LWConj2_gives : BackfillPaper6.V3.LWConj2_gives :=
  Paper6LouWang.check_LWConj2_gives
theorem check_ThmC_literal : BackfillPaper6.V3.ThmC_literal :=
  Paper6LiteralLouWang.check_ThmC_literal
theorem check_Sec4Concat : BackfillPaper6.V3.Sec4Concat := Paper6FirstBatch.check_Sec4Concat
theorem check_FactStar : BackfillPaper6.V3.FactStar := Paper6FactStar.check_FactStar
theorem check_TransversalDim : BackfillPaper6.V3.TransversalDim :=
  Paper6Geometry.check_TransversalDim
theorem check_PropD : BackfillPaper6.V3.PropD := Paper6ThreeFlats.check_PropD
theorem check_RemD162 : BackfillPaper6.V3.RemD162 := Paper6Remark162.check_RemD162
theorem check_PropE : BackfillPaper6.V3.PropE := Paper6FiveExclusion.check_PropE
theorem check_PropE_remark_2mod4 : BackfillPaper6.V3.PropE_remark_2mod4 :=
  Paper6RemarkWitnesses.check_PropE_remark_2mod4
theorem check_Lem51 : BackfillPaper6.V3.Lem51 := Paper6PairDecomposition.check_Lem51
theorem check_PropF : BackfillPaper6.V3.PropF := Paper6DirectionCriterion.check_PropF
theorem check_MinDist : BackfillPaper6.V3.MinDist := Paper6MinDistance.check_MinDist
theorem check_FlatBasics : BackfillPaper6.V3.FlatBasics := Paper6FlatBasics.check_FlatBasics
theorem check_AffineInvariance : BackfillPaper6.V3.AffineInvariance :=
  Paper6AffineInvariance.check_AffineInvariance
theorem check_Cat4Weight : BackfillPaper6.V3.Cat4Weight := Paper6Cat4Weight.check_Cat4Weight
theorem check_Calib612 : BackfillPaper6.V3.Calib612 := Paper6Calib.check_Calib612
theorem check_S0_eq_LA : BackfillPaper6.V3.S0_eq_LA := Paper6FirstBatch.check_S0_eq_LA
theorem check_ThmA_mathlib : BackfillPaper6.V3.ThmA_mathlib :=
  Paper6MathlibRestatementsV4.check_ThmA_mathlib
theorem check_PropE_mathlib : BackfillPaper6.V3.PropE_mathlib :=
  Paper6MathlibRestatementsV4.check_PropE_mathlib
theorem check_Sec7Bridge : BackfillPaper6.V3.Sec7Bridge :=
  Paper6ReleasedModelBridge.check_Sec7Bridge

end Paper6FinalPackageV4

#print axioms Paper6FinalPackageV4.check_P1
#print axioms Paper6FinalPackageV4.check_P2
#print axioms Paper6FinalPackageV4.check_P3_minWeight
#print axioms Paper6FinalPackageV4.check_Lem21
#print axioms Paper6FinalPackageV4.check_Lem21_venn
#print axioms Paper6FinalPackageV4.check_Lem22
#print axioms Paper6FinalPackageV4.check_ThmA
#print axioms Paper6FinalPackageV4.check_Table1
#print axioms Paper6FinalPackageV4.check_Rem31
#print axioms Paper6FinalPackageV4.check_ThmB_witnesses
#print axioms Paper6FinalPackageV4.check_S0_card
#print axioms Paper6FinalPackageV4.check_CarletEquiv
#print axioms Paper6FinalPackageV4.check_IntroMU
#print axioms Paper6FinalPackageV4.check_LAProp4
#print axioms Paper6FinalPackageV4.check_LWConstrInRM
#print axioms Paper6FinalPackageV4.check_LWConj2_gives
#print axioms Paper6FinalPackageV4.check_ThmC_literal
#print axioms Paper6FinalPackageV4.check_Sec4Concat
#print axioms Paper6FinalPackageV4.check_FactStar
#print axioms Paper6FinalPackageV4.check_TransversalDim
#print axioms Paper6FinalPackageV4.check_PropD
#print axioms Paper6FinalPackageV4.check_RemD162
#print axioms Paper6FinalPackageV4.check_PropE
#print axioms Paper6FinalPackageV4.check_PropE_remark_2mod4
#print axioms Paper6FinalPackageV4.check_Lem51
#print axioms Paper6FinalPackageV4.check_PropF
#print axioms Paper6FinalPackageV4.check_MinDist
#print axioms Paper6FinalPackageV4.check_FlatBasics
#print axioms Paper6FinalPackageV4.check_AffineInvariance
#print axioms Paper6FinalPackageV4.check_Cat4Weight
#print axioms Paper6FinalPackageV4.check_Calib612
#print axioms Paper6FinalPackageV4.check_S0_eq_LA
#print axioms Paper6FinalPackageV4.check_ThmA_mathlib
#print axioms Paper6FinalPackageV4.check_PropE_mathlib
#print axioms Paper6FinalPackageV4.check_Sec7Bridge
