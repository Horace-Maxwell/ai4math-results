import Research.Backfill.Paper3.Proof.Small.Labelled
import Research.Backfill.Paper3.Proof.Small.Failure
import Research.Backfill.Paper3.Proof.A.Main

/-!
# Paper 3, small graphs and exact counts: the checked statements

Each `check_X` has exactly the type of the frozen statement `BackfillPaper3.Challenge.X` (v2).
Proofs in `Research.Backfill.Paper3.Proof.Small.Tables`, `.Cubic`, `.Labelled`, `.Failure`; the finite computations are
kernel evaluations of the bit-mask checkers of `Research.Backfill.Paper3.Proof.Small.Defs`, proved correct in
`Research.Backfill.Paper3.Proof.Small.Bridge`. `SmallestCounterexample` uses `P3A.check_TrivialCasesTrue` (`Research.Backfill.Paper3.Proof.A.Main`).
-/

set_option autoImplicit false

namespace P3Small

theorem check_Table1 : BackfillPaper3.Challenge.Table1 := table1
#print axioms check_Table1

theorem check_Table4Counts : BackfillPaper3.Challenge.Table4Counts := table4Counts
#print axioms check_Table4Counts

theorem check_CubicSix : BackfillPaper3.Challenge.CubicSix := cubicSix
#print axioms check_CubicSix

theorem check_ExactFailureSix : BackfillPaper3.Challenge.ExactFailureSix := exactFailureSix
#print axioms check_ExactFailureSix

theorem check_SmallestCounterexample : BackfillPaper3.Challenge.SmallestCounterexample :=
  smallestCounterexample P3A.check_TrivialCasesTrue
#print axioms check_SmallestCounterexample

theorem check_LabelledCounts : BackfillPaper3.Challenge.LabelledCounts := labelledCounts
#print axioms check_LabelledCounts

end P3Small
