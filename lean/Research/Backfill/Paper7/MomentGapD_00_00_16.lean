import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C16

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

theorem row_00_00_16_00 : b4RowContribution (![0, 0, 16, 16] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨16, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 16, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_16_16
#print axioms Paper7MomentGapNumeric.row_00_00_16_00

theorem weighted_00_00_16_00 : b4RawGapContribution ![0, 0, 16, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 16, 0] = b4GapPatternWeight 0 16 0 * 0 :=
      b4GapContribution_from_row 0 0 16 0 0 row_00_00_16_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_16_00

theorem row_00_00_16_01 : b4RowContribution (![0, 0, 16, 17] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨16, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 16, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_16_17
#print axioms Paper7MomentGapNumeric.row_00_00_16_01

theorem weighted_00_00_16_01 : b4RawGapContribution ![0, 0, 16, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 16, 1] = b4GapPatternWeight 0 16 1 * 0 :=
      b4GapContribution_from_row 0 0 16 1 0 row_00_00_16_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_16_01

theorem row_00_00_16_02 : b4RowContribution (![0, 0, 16, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨16, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 16, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_16_18
#print axioms Paper7MomentGapNumeric.row_00_00_16_02

theorem weighted_00_00_16_02 : b4RawGapContribution ![0, 0, 16, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 16, 2] = b4GapPatternWeight 0 16 2 * 0 :=
      b4GapContribution_from_row 0 0 16 2 0 row_00_00_16_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_16_02

theorem row_00_00_16_03 : b4RowContribution (![0, 0, 16, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨16, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 16, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_16_19
#print axioms Paper7MomentGapNumeric.row_00_00_16_03

theorem weighted_00_00_16_03 : b4RawGapContribution ![0, 0, 16, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 16, 3] = b4GapPatternWeight 0 16 3 * 0 :=
      b4GapContribution_from_row 0 0 16 3 0 row_00_00_16_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_16_03

theorem row_00_00_16_04 : b4RowContribution (![0, 0, 16, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨16, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 16, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_16_20
#print axioms Paper7MomentGapNumeric.row_00_00_16_04

theorem weighted_00_00_16_04 : b4RawGapContribution ![0, 0, 16, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 16, 4] = b4GapPatternWeight 0 16 4 * 0 :=
      b4GapContribution_from_row 0 0 16 4 0 row_00_00_16_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_16_04

theorem row_00_00_16_05 : b4RowContribution (![0, 0, 16, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨16, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 16, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_16_21
#print axioms Paper7MomentGapNumeric.row_00_00_16_05

theorem weighted_00_00_16_05 : b4RawGapContribution ![0, 0, 16, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 16, 5] = b4GapPatternWeight 0 16 5 * 0 :=
      b4GapContribution_from_row 0 0 16 5 0 row_00_00_16_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_16_05

def dvalues_00_00_16 : Fin 6 → ℕ := ![0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_16

theorem dblock_00_00_16 : b4GapPatternDBlock 0 0 16 = 0 := by
  calc
    b4GapPatternDBlock 0 0 16 = ∑ d : Fin 6, dvalues_00_00_16 d := by
      apply b4GapDBlock_of_rows 0 0 16 dvalues_00_00_16
      intro d
      fin_cases d
      · exact weighted_00_00_16_00
      · exact weighted_00_00_16_01
      · exact weighted_00_00_16_02
      · exact weighted_00_00_16_03
      · exact weighted_00_00_16_04
      · exact weighted_00_00_16_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_16

end Paper7MomentGapNumeric
