import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapC_02_00
import Research.Backfill.Paper7.MomentGapC_02_01
import Research.Backfill.Paper7.MomentGapC_02_02
import Research.Backfill.Paper7.MomentGapC_02_03
import Research.Backfill.Paper7.MomentGapC_02_04
import Research.Backfill.Paper7.MomentGapC_02_05
import Research.Backfill.Paper7.MomentGapC_02_06
import Research.Backfill.Paper7.MomentGapC_02_07
import Research.Backfill.Paper7.MomentGapC_02_08
import Research.Backfill.Paper7.MomentGapC_02_09

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

def avalues_02 : Fin 10 → ℕ := ![14378, 30988, 20388, 11052, 10272, 5052, 3708, 228, 0, 0]
#print axioms Paper7MomentGapNumeric.avalues_02

theorem ablock_02 : b4GapABlock 2 = 96066 := by
  calc
    b4GapABlock 2 = ∑ i : Fin 10, avalues_02 i := by
      apply b4GapABlock_of_cblocks 2 avalues_02
      intro i
      fin_cases i
      · exact cblock_02_00
      · exact cblock_02_01
      · exact cblock_02_02
      · exact cblock_02_03
      · exact cblock_02_04
      · exact cblock_02_05
      · exact cblock_02_06
      · exact cblock_02_07
      · exact cblock_02_08
      · exact cblock_02_09
    _ = 96066 := by decide
#print axioms Paper7MomentGapNumeric.ablock_02

end Paper7MomentGapNumeric
