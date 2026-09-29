import Research.Backfill.Paper3.Proof.B.Cor5
import Research.Backfill.Paper3.Proof.B.Small

/-!
# Theorem B, Corollary 5, `S3PrismH2Cycle` and `Neg_2d`

`TheoremB` and `Neg_2d` (`Research.Backfill.Paper3.Proof.B.TheoremB`), `Corollary5` (`Research.Backfill.Paper3.Proof.B.Cor5`) and `S3PrismH2Cycle`
(`Research.Backfill.Paper3.Proof.B.Small`), each stated exactly as the frozen statement.
-/

set_option autoImplicit false

namespace P3B

theorem check_TheoremB : BackfillPaper3.Challenge.TheoremB := theoremB

#print axioms check_TheoremB

theorem check_Corollary5 : BackfillPaper3.Challenge.Corollary5 := corollary5

#print axioms check_Corollary5

theorem check_S3PrismH2Cycle : BackfillPaper3.Challenge.S3PrismH2Cycle := s3PrismH2Cycle

#print axioms check_S3PrismH2Cycle

theorem check_Neg_2d : BackfillPaper3.Challenge.Neg_2d := neg_2d

#print axioms check_Neg_2d

end P3B
