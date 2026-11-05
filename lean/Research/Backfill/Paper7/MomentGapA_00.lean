import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapC_00_00
import Research.Backfill.Paper7.MomentGapC_00_01
import Research.Backfill.Paper7.MomentGapC_00_02
import Research.Backfill.Paper7.MomentGapC_00_03
import Research.Backfill.Paper7.MomentGapC_00_04
import Research.Backfill.Paper7.MomentGapC_00_05
import Research.Backfill.Paper7.MomentGapC_00_06
import Research.Backfill.Paper7.MomentGapC_00_07
import Research.Backfill.Paper7.MomentGapC_00_08
import Research.Backfill.Paper7.MomentGapC_00_09
import Research.Backfill.Paper7.MomentGapC_00_10
import Research.Backfill.Paper7.MomentGapC_00_11
import Research.Backfill.Paper7.MomentGapC_00_12

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

def avalues_00 : Fin 13 → ℕ := ![3742, 13104, 15096, 15700, 13176, 10968, 7224, 7428, 2580, 1080, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.avalues_00

theorem ablock_00 : b4GapABlock 0 = 90098 := by
  calc
    b4GapABlock 0 = ∑ i : Fin 13, avalues_00 i := by
      apply b4GapABlock_of_cblocks 0 avalues_00
      intro i
      fin_cases i
      · exact cblock_00_00
      · exact cblock_00_01
      · exact cblock_00_02
      · exact cblock_00_03
      · exact cblock_00_04
      · exact cblock_00_05
      · exact cblock_00_06
      · exact cblock_00_07
      · exact cblock_00_08
      · exact cblock_00_09
      · exact cblock_00_10
      · exact cblock_00_11
      · exact cblock_00_12
    _ = 90098 := by decide
#print axioms Paper7MomentGapNumeric.ablock_00

end Paper7MomentGapNumeric
