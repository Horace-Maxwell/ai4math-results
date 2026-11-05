import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapC_01_00
import Research.Backfill.Paper7.MomentGapC_01_01
import Research.Backfill.Paper7.MomentGapC_01_02
import Research.Backfill.Paper7.MomentGapC_01_03
import Research.Backfill.Paper7.MomentGapC_01_04
import Research.Backfill.Paper7.MomentGapC_01_05
import Research.Backfill.Paper7.MomentGapC_01_06
import Research.Backfill.Paper7.MomentGapC_01_07
import Research.Backfill.Paper7.MomentGapC_01_08
import Research.Backfill.Paper7.MomentGapC_01_09
import Research.Backfill.Paper7.MomentGapC_01_10
import Research.Backfill.Paper7.MomentGapC_01_11

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

def avalues_01 : Fin 12 → ℕ := ![11018, 22680, 23544, 19308, 18444, 11052, 5832, 2928, 1032, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.avalues_01

theorem ablock_01 : b4GapABlock 1 = 115838 := by
  calc
    b4GapABlock 1 = ∑ i : Fin 12, avalues_01 i := by
      apply b4GapABlock_of_cblocks 1 avalues_01
      intro i
      fin_cases i
      · exact cblock_01_00
      · exact cblock_01_01
      · exact cblock_01_02
      · exact cblock_01_03
      · exact cblock_01_04
      · exact cblock_01_05
      · exact cblock_01_06
      · exact cblock_01_07
      · exact cblock_01_08
      · exact cblock_01_09
      · exact cblock_01_10
      · exact cblock_01_11
    _ = 115838 := by decide
#print axioms Paper7MomentGapNumeric.ablock_01

end Paper7MomentGapNumeric
