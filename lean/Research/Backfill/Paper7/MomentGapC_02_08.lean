import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_02_08_00
import Research.Backfill.Paper7.MomentGapD_02_08_01
import Research.Backfill.Paper7.MomentGapD_02_08_02

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

def cvalues_02_08 : Fin 3 → ℕ := ![0, 0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_02_08

theorem cblock_02_08 : b4GapCBlock 2 8 = 0 := by
  calc
    b4GapCBlock 2 8 = ∑ i : Fin 3, cvalues_02_08 i := by
      apply b4GapCBlock_of_dblocks 2 8 cvalues_02_08
      intro i
      fin_cases i
      · exact dblock_02_08_00
      · exact dblock_02_08_01
      · exact dblock_02_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.cblock_02_08

end Paper7MomentGapNumeric
