import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.MomentGapD_06_04_00

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

def cvalues_06_04 : Fin 1 → ℕ := ![0]
#print axioms Paper7MomentGapNumeric.cvalues_06_04

theorem cblock_06_04 : b4GapCBlock 6 4 = 0 := by
  calc
    b4GapCBlock 6 4 = ∑ i : Fin 1, cvalues_06_04 i := by
      apply b4GapCBlock_of_dblocks 6 4 cvalues_06_04
      intro i
      fin_cases i
      · exact dblock_06_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.cblock_06_04

end Paper7MomentGapNumeric
