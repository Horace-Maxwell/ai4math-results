import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_00_08_00
import Research.Backfill.Paper7.MomentGapD_00_08_01
import Research.Backfill.Paper7.MomentGapD_00_08_02
import Research.Backfill.Paper7.MomentGapD_00_08_03
import Research.Backfill.Paper7.MomentGapD_00_08_04
import Research.Backfill.Paper7.MomentGapD_00_08_05
import Research.Backfill.Paper7.MomentGapD_00_08_06

/-! Generated UNTRUSTED proof-source candidate. Fixed-file flags, native
totals, table completeness and a representative count are not hypotheses.
Every actual row, Q decision, DP cell and complete finite range is checked
by the eventual Lean proofs. Generation alone confers no credit. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentGapNumeric
open Paper7MomentCertificate Paper7MomentCounts Paper7MomentDP
open Paper7MomentReduction Paper7SortedGaps
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def cvalues_00_08 : Fin 7 → ℕ := ![1176, 732, 672, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_00_08

theorem cblock_00_08 : b4GapCBlock 0 8 = 2580 := by
  calc
    b4GapCBlock 0 8 = ∑ i : Fin 7, cvalues_00_08 i := by
      apply b4GapCBlock_of_dblocks 0 8 cvalues_00_08
      intro i
      fin_cases i
      · exact dblock_00_08_00
      · exact dblock_00_08_01
      · exact dblock_00_08_02
      · exact dblock_00_08_03
      · exact dblock_00_08_04
      · exact dblock_00_08_05
      · exact dblock_00_08_06
    _ = 2580 := by decide
#print axioms Paper7MomentGapNumeric.cblock_00_08

end Paper7MomentGapNumeric
