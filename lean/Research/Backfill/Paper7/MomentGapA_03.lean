import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapC_03_00
import Research.Backfill.Paper7.MomentGapC_03_01
import Research.Backfill.Paper7.MomentGapC_03_02
import Research.Backfill.Paper7.MomentGapC_03_03
import Research.Backfill.Paper7.MomentGapC_03_04
import Research.Backfill.Paper7.MomentGapC_03_05
import Research.Backfill.Paper7.MomentGapC_03_06
import Research.Backfill.Paper7.MomentGapC_03_07
import Research.Backfill.Paper7.MomentGapC_03_08

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

def avalues_03 : Fin 9 → ℕ := ![9628, 24540, 8712, 7872, 7560, 684, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.avalues_03

theorem ablock_03 : b4GapABlock 3 = 58996 := by
  calc
    b4GapABlock 3 = ∑ i : Fin 9, avalues_03 i := by
      apply b4GapABlock_of_cblocks 3 avalues_03
      intro i
      fin_cases i
      · exact cblock_03_00
      · exact cblock_03_01
      · exact cblock_03_02
      · exact cblock_03_03
      · exact cblock_03_04
      · exact cblock_03_05
      · exact cblock_03_06
      · exact cblock_03_07
      · exact cblock_03_08
    _ = 58996 := by decide
#print axioms Paper7MomentGapNumeric.ablock_03

end Paper7MomentGapNumeric
