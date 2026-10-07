import Research.Backfill.Paper5.Supplement.AlgebraStatementV2
import Research.Backfill.Paper5.Proof.HalfCounting

set_option autoImplicit false

namespace CodexPaper5.NumericHalfCounts

open BackfillPaper5

theorem check_HalfCount45 : CodexPaper5.AlgebraStatement.HalfCount45 := by
  change (Challenge.Hr Challenge.Fam.B 6 2).ncard = 45
  rw [CodexPaper5.HalfCounting.ncard_Hr_B 6 2 (by decide) (by decide)]
  decide

theorem check_HalfCount105 : CodexPaper5.AlgebraStatement.HalfCount105 := by
  change (Challenge.Hr Challenge.Fam.B 7 3).ncard = 105
  rw [CodexPaper5.HalfCounting.ncard_Hr_B 7 3 (by decide) (by decide)]
  decide

end CodexPaper5.NumericHalfCounts

#print axioms CodexPaper5.NumericHalfCounts.check_HalfCount45
#print axioms CodexPaper5.NumericHalfCounts.check_HalfCount105
