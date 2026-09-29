import Research.Backfill.Paper3.Proof.A.Remark4

/-!
# Paper 3, Theorem A cluster: the checked statements

Each `check_X` has exactly the type of the frozen statement `BackfillPaper3.Challenge.X`
(statement file version 2). Proofs: `Research.Backfill.Paper3.Proof.A.Lemma1` (Lemma 1, high-threshold tie),
`Research.Backfill.Paper3.Proof.A.Prop2` (Proposition 2), `Research.Backfill.Paper3.Proof.A.Lemma3`, `Research.Backfill.Paper3.Proof.A.TwoRegular`, `Research.Backfill.Paper3.Proof.A.Remark4` (Lemma 3,
Remark 4), `Research.Backfill.Paper3.Proof.A.TheoremA` (Theorem A, maximisers at `γ*`), `Research.Backfill.Paper3.Proof.A.Consequences` (competitors,
negative answers, scope of `γ*`, trivial cases, connectivity).
-/

set_option autoImplicit false

namespace P3A

theorem check_Lemma1 : BackfillPaper3.Challenge.Lemma1 := lemma1
#print axioms check_Lemma1

theorem check_Proposition2 : BackfillPaper3.Challenge.Proposition2 := proposition2
#print axioms check_Proposition2

theorem check_Lemma3 : BackfillPaper3.Challenge.Lemma3 := lemma3
#print axioms check_Lemma3

theorem check_TheoremA : BackfillPaper3.Challenge.TheoremA := theoremA
#print axioms check_TheoremA

theorem check_Remark4 : BackfillPaper3.Challenge.Remark4 := remark4
#print axioms check_Remark4

theorem check_CompetitorFacts : BackfillPaper3.Challenge.CompetitorFacts := competitorFacts
#print axioms check_CompetitorFacts

theorem check_NegativeEveryAdmissible : BackfillPaper3.Challenge.NegativeEveryAdmissible :=
  negativeEveryAdmissible
#print axioms check_NegativeEveryAdmissible

theorem check_GammaStarScope : BackfillPaper3.Challenge.GammaStarScope := gammaStarScope
#print axioms check_GammaStarScope

theorem check_MaximisersAtGammaStar : BackfillPaper3.Challenge.MaximisersAtGammaStar :=
  maximisersAtGammaStar
#print axioms check_MaximisersAtGammaStar

theorem check_HighThresholdTie : BackfillPaper3.Challenge.HighThresholdTie := highThresholdTie
#print axioms check_HighThresholdTie

theorem check_RegularOn2dConnected : BackfillPaper3.Challenge.RegularOn2dConnected :=
  regularOn2dConnected
#print axioms check_RegularOn2dConnected

theorem check_TrivialCasesUnique : BackfillPaper3.Challenge.TrivialCasesUnique :=
  trivialCasesUnique
#print axioms check_TrivialCasesUnique

theorem check_TrivialCasesTrue : BackfillPaper3.Challenge.TrivialCasesTrue := trivialCasesTrue
#print axioms check_TrivialCasesTrue

theorem check_Neg_6_3 : BackfillPaper3.Challenge.Neg_6_3 := neg_6_3
#print axioms check_Neg_6_3

theorem check_Neg_12_3_top : BackfillPaper3.Challenge.Neg_12_3_top := neg_12_3_top
#print axioms check_Neg_12_3_top

theorem check_AnswerNegative : BackfillPaper3.Challenge.AnswerNegative := answerNegative
#print axioms check_AnswerNegative

end P3A
