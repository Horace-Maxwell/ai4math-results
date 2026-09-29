import Research.Backfill.Paper3.Challenge
import Research.Backfill.Paper3.Proof.A.Main
import Research.Backfill.Paper3.Proof.B.Main
import Research.Backfill.Paper3.Proof.Basic
import Research.Backfill.Paper3.Proof.CD.Main
import Research.Backfill.Paper3.Proof.L67.Main
import Research.Backfill.Paper3.Proof.L8.Main
import Research.Backfill.Paper3.Proof.Num.Main
import Research.Backfill.Paper3.Proof.Poly
import Research.Backfill.Paper3.Proof.Remark10d
import Research.Backfill.Paper3.Proof.SSSZ.Main
import Research.Backfill.Paper3.Proof.Small.Main
import Research.Backfill.Paper3.Proof.TS.Main
import Research.Backfill.Paper3.Proof.Tier0

/-!
# Paper 3, version 2: the 60 statements of the frozen statement file are proved

Frozen statement file `Research/Backfill/Paper3/Challenge.lean`, SHA-256
`846efb56558f734ba475092854effbe7598549b68e6ea8b7bcad19e9c02d8777`.
Every theorem below has as its type exactly one frozen `def … : Prop` of that file. The proofs are
in `Research/Backfill/Paper3/Proof/`. Most use other frozen statements through the modules that
prove them; the proofs of `PropositionC`, `TheoremD`, `Remark10c`, `ReadingR6`, `Remark11` take other
frozen statements as explicit hypotheses, which are supplied here from their check theorems.
Proofs written by Claude Code agents, 29 September 2026.
-/

set_option autoImplicit false

namespace BackfillPaper3.Check

open BackfillPaper3

theorem check_IGammaFloor : Challenge.IGammaFloor := P3Basic.check_IGammaFloor
theorem check_IGammaIso : Challenge.IGammaIso := P3Basic.check_IGammaIso
theorem check_PolyFacts : Challenge.PolyFacts := P3Basic.check_PolyFacts
theorem check_IntegerForm : Challenge.IntegerForm := P3Basic.check_IntegerForm
theorem check_Neg_6_3 : Challenge.Neg_6_3 := P3A.check_Neg_6_3
theorem check_Neg_2d : Challenge.Neg_2d := P3B.check_Neg_2d
theorem check_Neg_8_2 : Challenge.Neg_8_2 := P3L67.check_Neg_8_2
theorem check_Neg_12_3_bip : Challenge.Neg_12_3_bip := P3L67.check_Neg_12_3_bip
theorem check_Neg_12_3_top : Challenge.Neg_12_3_top := P3A.check_Neg_12_3_top
theorem check_Table4Counts : Challenge.Table4Counts := P3Small.check_Table4Counts
theorem check_KddIndependentSets : Challenge.KddIndependentSets := P3Basic.check_KddIndependentSets
theorem check_Lemma1 : Challenge.Lemma1 := P3A.check_Lemma1
theorem check_Proposition2 : Challenge.Proposition2 := P3A.check_Proposition2
theorem check_Lemma3 : Challenge.Lemma3 := P3A.check_Lemma3
theorem check_TheoremA : Challenge.TheoremA := P3A.check_TheoremA
theorem check_Remark4 : Challenge.Remark4 := P3A.check_Remark4
theorem check_TheoremB : Challenge.TheoremB := P3B.check_TheoremB
theorem check_Corollary5 : Challenge.Corollary5 := P3B.check_Corollary5
theorem check_WSymm : Challenge.WSymm := P3L67.check_WSymm
theorem check_Lemma6 : Challenge.Lemma6 := P3L67.check_Lemma6
theorem check_Lemma7 : Challenge.Lemma7 := P3L67.check_Lemma7
theorem check_TheoremBprime : Challenge.TheoremBprime := P3L67.check_TheoremBprime
theorem check_Lemma8 : Challenge.Lemma8 := P3L8.check_Lemma8
theorem check_Lemma8_bddBelow : Challenge.Lemma8_bddBelow := P3L8.check_Lemma8_bddBelow
theorem check_SSSZBound : Challenge.SSSZBound := P3SSSZ.check_SSSZBound
theorem check_PropositionC : Challenge.PropositionC := P3CD.check_PropositionC check_SSSZBound check_Lemma8
theorem check_Rho_bddBelow : Challenge.Rho_bddBelow := P3CD.check_Rho_bddBelow
theorem check_TheoremD : Challenge.TheoremD := P3CD.check_TheoremD check_TheoremBprime check_Lemma8 check_Lemma6 check_Lemma7
theorem check_CareniniProp21 : Challenge.CareniniProp21 := P3SSSZ.check_CareniniProp21
theorem check_KahnZhao : Challenge.KahnZhao := P3SSSZ.check_KahnZhao
theorem check_QuestionTrueHalf : Challenge.QuestionTrueHalf := P3Basic.check_QuestionTrueHalf
theorem check_QuestionTrueZero : Challenge.QuestionTrueZero := P3SSSZ.check_QuestionTrueZero
theorem check_TrivialCasesUnique : Challenge.TrivialCasesUnique := P3A.check_TrivialCasesUnique
theorem check_TrivialCasesTrue : Challenge.TrivialCasesTrue := P3A.check_TrivialCasesTrue
theorem check_CompetitorFacts : Challenge.CompetitorFacts := P3A.check_CompetitorFacts
theorem check_NegativeEveryAdmissible : Challenge.NegativeEveryAdmissible := P3A.check_NegativeEveryAdmissible
theorem check_AnswerNegative : Challenge.AnswerNegative := P3A.check_AnswerNegative
theorem check_GammaStarScope : Challenge.GammaStarScope := P3A.check_GammaStarScope
theorem check_LowGammaExamples : Challenge.LowGammaExamples := P3Basic.check_LowGammaExamples
theorem check_S3PrismH2Cycle : Challenge.S3PrismH2Cycle := P3B.check_S3PrismH2Cycle
theorem check_SethDensity : Challenge.SethDensity := P3Basic.check_SethDensity
theorem check_MaximisersAtGammaStar : Challenge.MaximisersAtGammaStar := P3A.check_MaximisersAtGammaStar
theorem check_Table1 : Challenge.Table1 := P3Small.check_Table1
theorem check_CubicSix : Challenge.CubicSix := P3Small.check_CubicSix
theorem check_ExactFailureSix : Challenge.ExactFailureSix := P3Small.check_ExactFailureSix
theorem check_SmallestCounterexample : Challenge.SmallestCounterexample := P3Small.check_SmallestCounterexample
theorem check_Remark9 : Challenge.Remark9 := P3CD.check_Remark9
theorem check_Remark10a : Challenge.Remark10a := P3CD.check_Remark10a
theorem check_Remark10b : Challenge.Remark10b := P3Num.check_Remark10b
theorem check_Remark10c : Challenge.Remark10c := P3CD.check_Remark10c check_Lemma6
theorem check_Remark10d : Challenge.Remark10d := P3Basic.check_Remark10d
theorem check_ReadingR6 : Challenge.ReadingR6 := P3CD.check_ReadingR6 check_QuestionTrueZero
theorem check_Remark11 : Challenge.Remark11 := P3CD.check_Remark11 check_Lemma8 check_Lemma6 check_Lemma7
theorem check_Remark12 : Challenge.Remark12 := P3Num.check_Remark12
theorem check_RegularOn2dConnected : Challenge.RegularOn2dConnected := P3A.check_RegularOn2dConnected
theorem check_HighThresholdTie : Challenge.HighThresholdTie := P3A.check_HighThresholdTie
theorem check_TwoSwitchConnected : Challenge.TwoSwitchConnected := P3TS.check_TwoSwitchConnected
theorem check_Table2 : Challenge.Table2 := P3TS.check_Table2
theorem check_LabelledCounts : Challenge.LabelledCounts := P3Small.check_LabelledCounts
theorem check_TheoremDNumerics : Challenge.TheoremDNumerics := P3Num.check_TheoremDNumerics

#print axioms check_IGammaFloor
#print axioms check_IGammaIso
#print axioms check_PolyFacts
#print axioms check_IntegerForm
#print axioms check_Neg_6_3
#print axioms check_Neg_2d
#print axioms check_Neg_8_2
#print axioms check_Neg_12_3_bip
#print axioms check_Neg_12_3_top
#print axioms check_Table4Counts
#print axioms check_KddIndependentSets
#print axioms check_Lemma1
#print axioms check_Proposition2
#print axioms check_Lemma3
#print axioms check_TheoremA
#print axioms check_Remark4
#print axioms check_TheoremB
#print axioms check_Corollary5
#print axioms check_WSymm
#print axioms check_Lemma6
#print axioms check_Lemma7
#print axioms check_TheoremBprime
#print axioms check_Lemma8
#print axioms check_Lemma8_bddBelow
#print axioms check_PropositionC
#print axioms check_Rho_bddBelow
#print axioms check_TheoremD
#print axioms check_SSSZBound
#print axioms check_CareniniProp21
#print axioms check_KahnZhao
#print axioms check_QuestionTrueHalf
#print axioms check_QuestionTrueZero
#print axioms check_TrivialCasesUnique
#print axioms check_TrivialCasesTrue
#print axioms check_CompetitorFacts
#print axioms check_NegativeEveryAdmissible
#print axioms check_AnswerNegative
#print axioms check_GammaStarScope
#print axioms check_LowGammaExamples
#print axioms check_S3PrismH2Cycle
#print axioms check_SethDensity
#print axioms check_MaximisersAtGammaStar
#print axioms check_Table1
#print axioms check_CubicSix
#print axioms check_ExactFailureSix
#print axioms check_SmallestCounterexample
#print axioms check_Remark9
#print axioms check_Remark10a
#print axioms check_Remark10b
#print axioms check_Remark10c
#print axioms check_Remark10d
#print axioms check_ReadingR6
#print axioms check_Remark11
#print axioms check_Remark12
#print axioms check_RegularOn2dConnected
#print axioms check_HighThresholdTie
#print axioms check_TwoSwitchConnected
#print axioms check_Table2
#print axioms check_LabelledCounts
#print axioms check_TheoremDNumerics

end BackfillPaper3.Check
