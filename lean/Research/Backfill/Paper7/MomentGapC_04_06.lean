import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_04_06_00
import Research.Backfill.Paper7.MomentGapD_04_06_01

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

def cvalues_04_06 : Fin 2 → ℕ := ![0, 0]
#print axioms Paper7MomentGapNumeric.cvalues_04_06

theorem cblock_04_06 : b4GapCBlock 4 6 = 0 := by
  calc
    b4GapCBlock 4 6 = ∑ i : Fin 2, cvalues_04_06 i := by
      apply b4GapCBlock_of_dblocks 4 6 cvalues_04_06
      intro i
      fin_cases i
      · exact dblock_04_06_00
      · exact dblock_04_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.cblock_04_06

end Paper7MomentGapNumeric
