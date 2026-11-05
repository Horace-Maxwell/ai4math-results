import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C15

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

theorem row_00_00_15_00 : b4RowContribution (![0, 0, 15, 15] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨15, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 15, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_15_15
#print axioms Paper7MomentGapNumeric.row_00_00_15_00

theorem weighted_00_00_15_00 : b4RawGapContribution ![0, 0, 15, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 15, 0] = b4GapPatternWeight 0 15 0 * 0 :=
      b4GapContribution_from_row 0 0 15 0 0 row_00_00_15_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_15_00

theorem row_00_00_15_01 : b4RowContribution (![0, 0, 15, 16] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨15, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 15, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_15_16
#print axioms Paper7MomentGapNumeric.row_00_00_15_01

theorem weighted_00_00_15_01 : b4RawGapContribution ![0, 0, 15, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 15, 1] = b4GapPatternWeight 0 15 1 * 0 :=
      b4GapContribution_from_row 0 0 15 1 0 row_00_00_15_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_15_01

theorem row_00_00_15_02 : b4RowContribution (![0, 0, 15, 17] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨15, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 15, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_15_17
#print axioms Paper7MomentGapNumeric.row_00_00_15_02

theorem weighted_00_00_15_02 : b4RawGapContribution ![0, 0, 15, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 15, 2] = b4GapPatternWeight 0 15 2 * 0 :=
      b4GapContribution_from_row 0 0 15 2 0 row_00_00_15_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_15_02

theorem row_00_00_15_03 : b4RowContribution (![0, 0, 15, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨15, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 15, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_15_18
#print axioms Paper7MomentGapNumeric.row_00_00_15_03

theorem weighted_00_00_15_03 : b4RawGapContribution ![0, 0, 15, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 15, 3] = b4GapPatternWeight 0 15 3 * 0 :=
      b4GapContribution_from_row 0 0 15 3 0 row_00_00_15_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_15_03

theorem row_00_00_15_04 : b4RowContribution (![0, 0, 15, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨15, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 15, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_15_19
#print axioms Paper7MomentGapNumeric.row_00_00_15_04

theorem weighted_00_00_15_04 : b4RawGapContribution ![0, 0, 15, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 15, 4] = b4GapPatternWeight 0 15 4 * 0 :=
      b4GapContribution_from_row 0 0 15 4 0 row_00_00_15_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_15_04

theorem row_00_00_15_05 : b4RowContribution (![0, 0, 15, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨15, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 15, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_15_20
#print axioms Paper7MomentGapNumeric.row_00_00_15_05

theorem weighted_00_00_15_05 : b4RawGapContribution ![0, 0, 15, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 15, 5] = b4GapPatternWeight 0 15 5 * 0 :=
      b4GapContribution_from_row 0 0 15 5 0 row_00_00_15_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_15_05

theorem row_00_00_15_06 : b4RowContribution (![0, 0, 15, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨15, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 15, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_15_21
#print axioms Paper7MomentGapNumeric.row_00_00_15_06

theorem weighted_00_00_15_06 : b4RawGapContribution ![0, 0, 15, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 15, 6] = b4GapPatternWeight 0 15 6 * 0 :=
      b4GapContribution_from_row 0 0 15 6 0 row_00_00_15_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_15_06

theorem row_00_00_15_07 : b4RowContribution (![0, 0, 15, 22] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨15, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 15, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_15_22
#print axioms Paper7MomentGapNumeric.row_00_00_15_07

theorem weighted_00_00_15_07 : b4RawGapContribution ![0, 0, 15, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 15, 7] = b4GapPatternWeight 0 15 7 * 0 :=
      b4GapContribution_from_row 0 0 15 7 0 row_00_00_15_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_15_07

def dvalues_00_00_15 : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_15

theorem dblock_00_00_15 : b4GapPatternDBlock 0 0 15 = 0 := by
  calc
    b4GapPatternDBlock 0 0 15 = ∑ d : Fin 8, dvalues_00_00_15 d := by
      apply b4GapDBlock_of_rows 0 0 15 dvalues_00_00_15
      intro d
      fin_cases d
      · exact weighted_00_00_15_00
      · exact weighted_00_00_15_01
      · exact weighted_00_00_15_02
      · exact weighted_00_00_15_03
      · exact weighted_00_00_15_04
      · exact weighted_00_00_15_05
      · exact weighted_00_00_15_06
      · exact weighted_00_00_15_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_15

end Paper7MomentGapNumeric
