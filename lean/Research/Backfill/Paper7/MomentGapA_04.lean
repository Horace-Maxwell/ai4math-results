import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapC_04_00
import Research.Backfill.Paper7.MomentGapC_04_01
import Research.Backfill.Paper7.MomentGapC_04_02
import Research.Backfill.Paper7.MomentGapC_04_03
import Research.Backfill.Paper7.MomentGapC_04_04
import Research.Backfill.Paper7.MomentGapC_04_05
import Research.Backfill.Paper7.MomentGapC_04_06
import Research.Backfill.Paper7.MomentGapC_04_07

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

def avalues_04 : Fin 8 → ℕ := ![8660, 11880, 7944, 1968, 1860, 660, 0, 0]
#print axioms Paper7MomentGapNumeric.avalues_04

theorem ablock_04 : b4GapABlock 4 = 32972 := by
  calc
    b4GapABlock 4 = ∑ i : Fin 8, avalues_04 i := by
      apply b4GapABlock_of_cblocks 4 avalues_04
      intro i
      fin_cases i
      · exact cblock_04_00
      · exact cblock_04_01
      · exact cblock_04_02
      · exact cblock_04_03
      · exact cblock_04_04
      · exact cblock_04_05
      · exact cblock_04_06
      · exact cblock_04_07
    _ = 32972 := by decide
#print axioms Paper7MomentGapNumeric.ablock_04

end Paper7MomentGapNumeric
