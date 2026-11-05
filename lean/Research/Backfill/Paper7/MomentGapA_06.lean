import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapC_06_00
import Research.Backfill.Paper7.MomentGapC_06_01
import Research.Backfill.Paper7.MomentGapC_06_02
import Research.Backfill.Paper7.MomentGapC_06_03
import Research.Backfill.Paper7.MomentGapC_06_04

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

def avalues_06 : Fin 5 → ℕ := ![2454, 684, 240, 80, 0]
#print axioms Paper7MomentGapNumeric.avalues_06

theorem ablock_06 : b4GapABlock 6 = 3458 := by
  calc
    b4GapABlock 6 = ∑ i : Fin 5, avalues_06 i := by
      apply b4GapABlock_of_cblocks 6 avalues_06
      intro i
      fin_cases i
      · exact cblock_06_00
      · exact cblock_06_01
      · exact cblock_06_02
      · exact cblock_06_03
      · exact cblock_06_04
    _ = 3458 := by decide
#print axioms Paper7MomentGapNumeric.ablock_06

end Paper7MomentGapNumeric
