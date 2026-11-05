import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_00_05_00
import Research.Backfill.Paper7.MomentGapD_00_05_01
import Research.Backfill.Paper7.MomentGapD_00_05_02
import Research.Backfill.Paper7.MomentGapD_00_05_03
import Research.Backfill.Paper7.MomentGapD_00_05_04
import Research.Backfill.Paper7.MomentGapD_00_05_05
import Research.Backfill.Paper7.MomentGapD_00_05_06
import Research.Backfill.Paper7.MomentGapD_00_05_07
import Research.Backfill.Paper7.MomentGapD_00_05_08
import Research.Backfill.Paper7.MomentGapD_00_05_09
import Research.Backfill.Paper7.MomentGapD_00_05_10
import Research.Backfill.Paper7.MomentGapD_00_05_11

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

def cvalues_00_05 : Fin 12 → ℕ := ![864, 2856, 1128, 2376, 2736, 1008, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_00_05

theorem cblock_00_05 : b4GapCBlock 0 5 = 10968 := by
  calc
    b4GapCBlock 0 5 = ∑ i : Fin 12, cvalues_00_05 i := by
      apply b4GapCBlock_of_dblocks 0 5 cvalues_00_05
      intro i
      fin_cases i
      · exact dblock_00_05_00
      · exact dblock_00_05_01
      · exact dblock_00_05_02
      · exact dblock_00_05_03
      · exact dblock_00_05_04
      · exact dblock_00_05_05
      · exact dblock_00_05_06
      · exact dblock_00_05_07
      · exact dblock_00_05_08
      · exact dblock_00_05_09
      · exact dblock_00_05_10
      · exact dblock_00_05_11
    _ = 10968 := by decide
#print axioms Paper7MomentGapNumeric.cblock_00_05

end Paper7MomentGapNumeric
