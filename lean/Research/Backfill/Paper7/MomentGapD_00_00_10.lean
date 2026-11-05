import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C10

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

theorem row_00_00_10_00 : b4RowContribution (![0, 0, 10, 10] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨10, by decide⟩⟩ = (![0, 0, 10, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_10
#print axioms Paper7MomentGapNumeric.row_00_00_10_00

theorem weighted_00_00_10_00 : b4RawGapContribution ![0, 0, 10, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 0] = b4GapPatternWeight 0 10 0 * 0 :=
      b4GapContribution_from_row 0 0 10 0 0 row_00_00_10_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_00

theorem row_00_00_10_01 : b4RowContribution (![0, 0, 10, 11] : Fin 4 → ℕ) = 17 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨11, by decide⟩⟩ = (![0, 0, 10, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_11
#print axioms Paper7MomentGapNumeric.row_00_00_10_01

theorem weighted_00_00_10_01 : b4RawGapContribution ![0, 0, 10, 1] = 204 := by
  calc
    b4RawGapContribution ![0, 0, 10, 1] = b4GapPatternWeight 0 10 1 * 17 :=
      b4GapContribution_from_row 0 0 10 1 17 row_00_00_10_01
    _ = 204 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_01

theorem row_00_00_10_02 : b4RowContribution (![0, 0, 10, 12] : Fin 4 → ℕ) = 8 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨12, by decide⟩⟩ = (![0, 0, 10, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_12
#print axioms Paper7MomentGapNumeric.row_00_00_10_02

theorem weighted_00_00_10_02 : b4RawGapContribution ![0, 0, 10, 2] = 96 := by
  calc
    b4RawGapContribution ![0, 0, 10, 2] = b4GapPatternWeight 0 10 2 * 8 :=
      b4GapContribution_from_row 0 0 10 2 8 row_00_00_10_02
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_02

theorem row_00_00_10_03 : b4RowContribution (![0, 0, 10, 13] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨13, by decide⟩⟩ = (![0, 0, 10, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_13
#print axioms Paper7MomentGapNumeric.row_00_00_10_03

theorem weighted_00_00_10_03 : b4RawGapContribution ![0, 0, 10, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 3] = b4GapPatternWeight 0 10 3 * 0 :=
      b4GapContribution_from_row 0 0 10 3 0 row_00_00_10_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_03

theorem row_00_00_10_04 : b4RowContribution (![0, 0, 10, 14] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨14, by decide⟩⟩ = (![0, 0, 10, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_14
#print axioms Paper7MomentGapNumeric.row_00_00_10_04

theorem weighted_00_00_10_04 : b4RawGapContribution ![0, 0, 10, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 4] = b4GapPatternWeight 0 10 4 * 0 :=
      b4GapContribution_from_row 0 0 10 4 0 row_00_00_10_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_04

theorem row_00_00_10_05 : b4RowContribution (![0, 0, 10, 15] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 10, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_15
#print axioms Paper7MomentGapNumeric.row_00_00_10_05

theorem weighted_00_00_10_05 : b4RawGapContribution ![0, 0, 10, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 5] = b4GapPatternWeight 0 10 5 * 0 :=
      b4GapContribution_from_row 0 0 10 5 0 row_00_00_10_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_05

theorem row_00_00_10_06 : b4RowContribution (![0, 0, 10, 16] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 10, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_16
#print axioms Paper7MomentGapNumeric.row_00_00_10_06

theorem weighted_00_00_10_06 : b4RawGapContribution ![0, 0, 10, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 6] = b4GapPatternWeight 0 10 6 * 0 :=
      b4GapContribution_from_row 0 0 10 6 0 row_00_00_10_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_06

theorem row_00_00_10_07 : b4RowContribution (![0, 0, 10, 17] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 10, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_17
#print axioms Paper7MomentGapNumeric.row_00_00_10_07

theorem weighted_00_00_10_07 : b4RawGapContribution ![0, 0, 10, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 7] = b4GapPatternWeight 0 10 7 * 0 :=
      b4GapContribution_from_row 0 0 10 7 0 row_00_00_10_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_07

theorem row_00_00_10_08 : b4RowContribution (![0, 0, 10, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 10, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_18
#print axioms Paper7MomentGapNumeric.row_00_00_10_08

theorem weighted_00_00_10_08 : b4RawGapContribution ![0, 0, 10, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 8] = b4GapPatternWeight 0 10 8 * 0 :=
      b4GapContribution_from_row 0 0 10 8 0 row_00_00_10_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_08

theorem row_00_00_10_09 : b4RowContribution (![0, 0, 10, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 10, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_19
#print axioms Paper7MomentGapNumeric.row_00_00_10_09

theorem weighted_00_00_10_09 : b4RawGapContribution ![0, 0, 10, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 9] = b4GapPatternWeight 0 10 9 * 0 :=
      b4GapContribution_from_row 0 0 10 9 0 row_00_00_10_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_09

theorem row_00_00_10_10 : b4RowContribution (![0, 0, 10, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 10, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_20
#print axioms Paper7MomentGapNumeric.row_00_00_10_10

theorem weighted_00_00_10_10 : b4RawGapContribution ![0, 0, 10, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 10] = b4GapPatternWeight 0 10 10 * 0 :=
      b4GapContribution_from_row 0 0 10 10 0 row_00_00_10_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_10

theorem row_00_00_10_11 : b4RowContribution (![0, 0, 10, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 10, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_21
#print axioms Paper7MomentGapNumeric.row_00_00_10_11

theorem weighted_00_00_10_11 : b4RawGapContribution ![0, 0, 10, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 11] = b4GapPatternWeight 0 10 11 * 0 :=
      b4GapContribution_from_row 0 0 10 11 0 row_00_00_10_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_11

theorem row_00_00_10_12 : b4RowContribution (![0, 0, 10, 22] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 10, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_22
#print axioms Paper7MomentGapNumeric.row_00_00_10_12

theorem weighted_00_00_10_12 : b4RawGapContribution ![0, 0, 10, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 12] = b4GapPatternWeight 0 10 12 * 0 :=
      b4GapContribution_from_row 0 0 10 12 0 row_00_00_10_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_12

theorem row_00_00_10_13 : b4RowContribution (![0, 0, 10, 23] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨23, by decide⟩⟩ = (![0, 0, 10, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_23
#print axioms Paper7MomentGapNumeric.row_00_00_10_13

theorem weighted_00_00_10_13 : b4RawGapContribution ![0, 0, 10, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 13] = b4GapPatternWeight 0 10 13 * 0 :=
      b4GapContribution_from_row 0 0 10 13 0 row_00_00_10_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_13

theorem row_00_00_10_14 : b4RowContribution (![0, 0, 10, 24] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨24, by decide⟩⟩ = (![0, 0, 10, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_24
#print axioms Paper7MomentGapNumeric.row_00_00_10_14

theorem weighted_00_00_10_14 : b4RawGapContribution ![0, 0, 10, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 14] = b4GapPatternWeight 0 10 14 * 0 :=
      b4GapContribution_from_row 0 0 10 14 0 row_00_00_10_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_14

theorem row_00_00_10_15 : b4RowContribution (![0, 0, 10, 25] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨25, by decide⟩⟩ = (![0, 0, 10, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_25
#print axioms Paper7MomentGapNumeric.row_00_00_10_15

theorem weighted_00_00_10_15 : b4RawGapContribution ![0, 0, 10, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 15] = b4GapPatternWeight 0 10 15 * 0 :=
      b4GapContribution_from_row 0 0 10 15 0 row_00_00_10_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_15

theorem row_00_00_10_16 : b4RowContribution (![0, 0, 10, 26] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨26, by decide⟩⟩ = (![0, 0, 10, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_26
#print axioms Paper7MomentGapNumeric.row_00_00_10_16

theorem weighted_00_00_10_16 : b4RawGapContribution ![0, 0, 10, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 16] = b4GapPatternWeight 0 10 16 * 0 :=
      b4GapContribution_from_row 0 0 10 16 0 row_00_00_10_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_16

theorem row_00_00_10_17 : b4RowContribution (![0, 0, 10, 27] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨10, by decide⟩, ⟨27, by decide⟩⟩ = (![0, 0, 10, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_10_27
#print axioms Paper7MomentGapNumeric.row_00_00_10_17

theorem weighted_00_00_10_17 : b4RawGapContribution ![0, 0, 10, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 10, 17] = b4GapPatternWeight 0 10 17 * 0 :=
      b4GapContribution_from_row 0 0 10 17 0 row_00_00_10_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_10_17

def dvalues_00_00_10 : Fin 18 → ℕ := ![0, 204, 96, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_10

theorem dblock_00_00_10 : b4GapPatternDBlock 0 0 10 = 300 := by
  calc
    b4GapPatternDBlock 0 0 10 = ∑ d : Fin 18, dvalues_00_00_10 d := by
      apply b4GapDBlock_of_rows 0 0 10 dvalues_00_00_10
      intro d
      fin_cases d
      · exact weighted_00_00_10_00
      · exact weighted_00_00_10_01
      · exact weighted_00_00_10_02
      · exact weighted_00_00_10_03
      · exact weighted_00_00_10_04
      · exact weighted_00_00_10_05
      · exact weighted_00_00_10_06
      · exact weighted_00_00_10_07
      · exact weighted_00_00_10_08
      · exact weighted_00_00_10_09
      · exact weighted_00_00_10_10
      · exact weighted_00_00_10_11
      · exact weighted_00_00_10_12
      · exact weighted_00_00_10_13
      · exact weighted_00_00_10_14
      · exact weighted_00_00_10_15
      · exact weighted_00_00_10_16
      · exact weighted_00_00_10_17
    _ = 300 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_10

end Paper7MomentGapNumeric
