import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_04_02_00
import Research.Backfill.Paper7.MomentGapD_04_02_01
import Research.Backfill.Paper7.MomentGapD_04_02_02
import Research.Backfill.Paper7.MomentGapD_04_02_03
import Research.Backfill.Paper7.MomentGapD_04_02_04
import Research.Backfill.Paper7.MomentGapD_04_02_05
import Research.Backfill.Paper7.MomentGapD_04_02_06
import Research.Backfill.Paper7.MomentGapD_04_02_07

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

def cvalues_04_02 : Fin 8 → ℕ := ![1080, 6024, 504, 336, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_04_02

theorem cblock_04_02 : b4GapCBlock 4 2 = 7944 := by
  calc
    b4GapCBlock 4 2 = ∑ i : Fin 8, cvalues_04_02 i := by
      apply b4GapCBlock_of_dblocks 4 2 cvalues_04_02
      intro i
      fin_cases i
      · exact dblock_04_02_00
      · exact dblock_04_02_01
      · exact dblock_04_02_02
      · exact dblock_04_02_03
      · exact dblock_04_02_04
      · exact dblock_04_02_05
      · exact dblock_04_02_06
      · exact dblock_04_02_07
    _ = 7944 := by decide
#print axioms Paper7MomentGapNumeric.cblock_04_02

end Paper7MomentGapNumeric
