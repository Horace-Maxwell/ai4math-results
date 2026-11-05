import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapC_05_00
import Research.Backfill.Paper7.MomentGapC_05_01
import Research.Backfill.Paper7.MomentGapC_05_02
import Research.Backfill.Paper7.MomentGapC_05_03
import Research.Backfill.Paper7.MomentGapC_05_04
import Research.Backfill.Paper7.MomentGapC_05_05

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

def avalues_05 : Fin 6 → ℕ := ![4152, 6348, 1896, 12, 0, 0]
#print axioms Paper7MomentGapNumeric.avalues_05

theorem ablock_05 : b4GapABlock 5 = 12408 := by
  calc
    b4GapABlock 5 = ∑ i : Fin 6, avalues_05 i := by
      apply b4GapABlock_of_cblocks 5 avalues_05
      intro i
      fin_cases i
      · exact cblock_05_00
      · exact cblock_05_01
      · exact cblock_05_02
      · exact cblock_05_03
      · exact cblock_05_04
      · exact cblock_05_05
    _ = 12408 := by decide
#print axioms Paper7MomentGapNumeric.ablock_05

end Paper7MomentGapNumeric
