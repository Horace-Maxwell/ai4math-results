import Research.Backfill.Paper3.Proof.TS.D3
import Research.Backfill.Paper3.Proof.TS.D4
import Research.Backfill.Paper3.Proof.TS.D5

/-!
# Table 2

The three rows `d = 3, 4, 5` (`Research.Backfill.Paper3.Proof.TS.D3`, `Research.Backfill.Paper3.Proof.TS.D4`, `Research.Backfill.Paper3.Proof.TS.D5`): the class counts 2, 6, 60 of
`d`-regular graphs on `Fin (2d)`, the failure thresholds of `K_{d,d}` with the maxima, and the
thresholds with a unique maximiser or a tie.
-/

set_option autoImplicit false

namespace P3TS

/-- **Table 2** (`BackfillPaper3.Challenge.Table2`). -/
theorem table2 : BackfillPaper3.Challenge.Table2 :=
  ⟨D3.row, D4.row, D5.row⟩

end P3TS
