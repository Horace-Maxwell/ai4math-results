import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C09

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

theorem row_00_00_09_00 : b4RowContribution (![0, 0, 9, 9] : Fin 4 → ℕ) = 1 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨9, by decide⟩⟩ = (![0, 0, 9, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_09
#print axioms Paper7MomentGapNumeric.row_00_00_09_00

theorem weighted_00_00_09_00 : b4RawGapContribution ![0, 0, 9, 0] = 6 := by
  calc
    b4RawGapContribution ![0, 0, 9, 0] = b4GapPatternWeight 0 9 0 * 1 :=
      b4GapContribution_from_row 0 0 9 0 1 row_00_00_09_00
    _ = 6 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_00

theorem row_00_00_09_01 : b4RowContribution (![0, 0, 9, 10] : Fin 4 → ℕ) = 8 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨10, by decide⟩⟩ = (![0, 0, 9, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_10
#print axioms Paper7MomentGapNumeric.row_00_00_09_01

theorem weighted_00_00_09_01 : b4RawGapContribution ![0, 0, 9, 1] = 96 := by
  calc
    b4RawGapContribution ![0, 0, 9, 1] = b4GapPatternWeight 0 9 1 * 8 :=
      b4GapContribution_from_row 0 0 9 1 8 row_00_00_09_01
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_01

theorem row_00_00_09_02 : b4RowContribution (![0, 0, 9, 11] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨11, by decide⟩⟩ = (![0, 0, 9, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_11
#print axioms Paper7MomentGapNumeric.row_00_00_09_02

theorem weighted_00_00_09_02 : b4RawGapContribution ![0, 0, 9, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 9, 2] = b4GapPatternWeight 0 9 2 * 0 :=
      b4GapContribution_from_row 0 0 9 2 0 row_00_00_09_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_02

theorem row_00_00_09_03 : b4RowContribution (![0, 0, 9, 12] : Fin 4 → ℕ) = 17 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨12, by decide⟩⟩ = (![0, 0, 9, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_12
#print axioms Paper7MomentGapNumeric.row_00_00_09_03

theorem weighted_00_00_09_03 : b4RawGapContribution ![0, 0, 9, 3] = 204 := by
  calc
    b4RawGapContribution ![0, 0, 9, 3] = b4GapPatternWeight 0 9 3 * 17 :=
      b4GapContribution_from_row 0 0 9 3 17 row_00_00_09_03
    _ = 204 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_03

theorem row_00_00_09_04 : b4RowContribution (![0, 0, 9, 13] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨13, by decide⟩⟩ = (![0, 0, 9, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_13
#print axioms Paper7MomentGapNumeric.row_00_00_09_04

theorem weighted_00_00_09_04 : b4RawGapContribution ![0, 0, 9, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 9, 4] = b4GapPatternWeight 0 9 4 * 0 :=
      b4GapContribution_from_row 0 0 9 4 0 row_00_00_09_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_04

theorem row_00_00_09_05 : b4RowContribution (![0, 0, 9, 14] : Fin 4 → ℕ) = 10 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨14, by decide⟩⟩ = (![0, 0, 9, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_14
#print axioms Paper7MomentGapNumeric.row_00_00_09_05

theorem weighted_00_00_09_05 : b4RawGapContribution ![0, 0, 9, 5] = 120 := by
  calc
    b4RawGapContribution ![0, 0, 9, 5] = b4GapPatternWeight 0 9 5 * 10 :=
      b4GapContribution_from_row 0 0 9 5 10 row_00_00_09_05
    _ = 120 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_05

theorem row_00_00_09_06 : b4RowContribution (![0, 0, 9, 15] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 9, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_15
#print axioms Paper7MomentGapNumeric.row_00_00_09_06

theorem weighted_00_00_09_06 : b4RawGapContribution ![0, 0, 9, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 9, 6] = b4GapPatternWeight 0 9 6 * 0 :=
      b4GapContribution_from_row 0 0 9 6 0 row_00_00_09_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_06

theorem row_00_00_09_07 : b4RowContribution (![0, 0, 9, 16] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 9, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_16
#print axioms Paper7MomentGapNumeric.row_00_00_09_07

theorem weighted_00_00_09_07 : b4RawGapContribution ![0, 0, 9, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 9, 7] = b4GapPatternWeight 0 9 7 * 0 :=
      b4GapContribution_from_row 0 0 9 7 0 row_00_00_09_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_07

theorem row_00_00_09_08 : b4RowContribution (![0, 0, 9, 17] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 9, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_17
#print axioms Paper7MomentGapNumeric.row_00_00_09_08

theorem weighted_00_00_09_08 : b4RawGapContribution ![0, 0, 9, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 9, 8] = b4GapPatternWeight 0 9 8 * 0 :=
      b4GapContribution_from_row 0 0 9 8 0 row_00_00_09_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_08

theorem row_00_00_09_09 : b4RowContribution (![0, 0, 9, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 9, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_18
#print axioms Paper7MomentGapNumeric.row_00_00_09_09

theorem weighted_00_00_09_09 : b4RawGapContribution ![0, 0, 9, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 9, 9] = b4GapPatternWeight 0 9 9 * 0 :=
      b4GapContribution_from_row 0 0 9 9 0 row_00_00_09_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_09

theorem row_00_00_09_10 : b4RowContribution (![0, 0, 9, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 9, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_19
#print axioms Paper7MomentGapNumeric.row_00_00_09_10

theorem weighted_00_00_09_10 : b4RawGapContribution ![0, 0, 9, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 9, 10] = b4GapPatternWeight 0 9 10 * 0 :=
      b4GapContribution_from_row 0 0 9 10 0 row_00_00_09_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_10

theorem row_00_00_09_11 : b4RowContribution (![0, 0, 9, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 9, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_20
#print axioms Paper7MomentGapNumeric.row_00_00_09_11

theorem weighted_00_00_09_11 : b4RawGapContribution ![0, 0, 9, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 9, 11] = b4GapPatternWeight 0 9 11 * 0 :=
      b4GapContribution_from_row 0 0 9 11 0 row_00_00_09_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_11

theorem row_00_00_09_12 : b4RowContribution (![0, 0, 9, 21] : Fin 4 → ℕ) = 1 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 9, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_21
#print axioms Paper7MomentGapNumeric.row_00_00_09_12

theorem weighted_00_00_09_12 : b4RawGapContribution ![0, 0, 9, 12] = 12 := by
  calc
    b4RawGapContribution ![0, 0, 9, 12] = b4GapPatternWeight 0 9 12 * 1 :=
      b4GapContribution_from_row 0 0 9 12 1 row_00_00_09_12
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_12

theorem row_00_00_09_13 : b4RowContribution (![0, 0, 9, 22] : Fin 4 → ℕ) = 2 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 9, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_22
#print axioms Paper7MomentGapNumeric.row_00_00_09_13

theorem weighted_00_00_09_13 : b4RawGapContribution ![0, 0, 9, 13] = 24 := by
  calc
    b4RawGapContribution ![0, 0, 9, 13] = b4GapPatternWeight 0 9 13 * 2 :=
      b4GapContribution_from_row 0 0 9 13 2 row_00_00_09_13
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_13

theorem row_00_00_09_14 : b4RowContribution (![0, 0, 9, 23] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨23, by decide⟩⟩ = (![0, 0, 9, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_23
#print axioms Paper7MomentGapNumeric.row_00_00_09_14

theorem weighted_00_00_09_14 : b4RawGapContribution ![0, 0, 9, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 9, 14] = b4GapPatternWeight 0 9 14 * 0 :=
      b4GapContribution_from_row 0 0 9 14 0 row_00_00_09_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_14

theorem row_00_00_09_15 : b4RowContribution (![0, 0, 9, 24] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨24, by decide⟩⟩ = (![0, 0, 9, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_24
#print axioms Paper7MomentGapNumeric.row_00_00_09_15

theorem weighted_00_00_09_15 : b4RawGapContribution ![0, 0, 9, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 9, 15] = b4GapPatternWeight 0 9 15 * 0 :=
      b4GapContribution_from_row 0 0 9 15 0 row_00_00_09_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_15

theorem row_00_00_09_16 : b4RowContribution (![0, 0, 9, 25] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨25, by decide⟩⟩ = (![0, 0, 9, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_25
#print axioms Paper7MomentGapNumeric.row_00_00_09_16

theorem weighted_00_00_09_16 : b4RawGapContribution ![0, 0, 9, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 9, 16] = b4GapPatternWeight 0 9 16 * 0 :=
      b4GapContribution_from_row 0 0 9 16 0 row_00_00_09_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_16

theorem row_00_00_09_17 : b4RowContribution (![0, 0, 9, 26] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨26, by decide⟩⟩ = (![0, 0, 9, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_26
#print axioms Paper7MomentGapNumeric.row_00_00_09_17

theorem weighted_00_00_09_17 : b4RawGapContribution ![0, 0, 9, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 9, 17] = b4GapPatternWeight 0 9 17 * 0 :=
      b4GapContribution_from_row 0 0 9 17 0 row_00_00_09_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_17

theorem row_00_00_09_18 : b4RowContribution (![0, 0, 9, 27] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨27, by decide⟩⟩ = (![0, 0, 9, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_27
#print axioms Paper7MomentGapNumeric.row_00_00_09_18

theorem weighted_00_00_09_18 : b4RawGapContribution ![0, 0, 9, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 9, 18] = b4GapPatternWeight 0 9 18 * 0 :=
      b4GapContribution_from_row 0 0 9 18 0 row_00_00_09_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_18

theorem row_00_00_09_19 : b4RowContribution (![0, 0, 9, 28] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨9, by decide⟩, ⟨28, by decide⟩⟩ = (![0, 0, 9, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_09_28
#print axioms Paper7MomentGapNumeric.row_00_00_09_19

theorem weighted_00_00_09_19 : b4RawGapContribution ![0, 0, 9, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 9, 19] = b4GapPatternWeight 0 9 19 * 0 :=
      b4GapContribution_from_row 0 0 9 19 0 row_00_00_09_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_09_19

def dvalues_00_00_09 : Fin 20 → ℕ := ![6, 96, 0, 204, 0, 120, 0, 0, 0, 0, 0, 0, 12, 24, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_09

theorem dblock_00_00_09 : b4GapPatternDBlock 0 0 9 = 462 := by
  calc
    b4GapPatternDBlock 0 0 9 = ∑ d : Fin 20, dvalues_00_00_09 d := by
      apply b4GapDBlock_of_rows 0 0 9 dvalues_00_00_09
      intro d
      fin_cases d
      · exact weighted_00_00_09_00
      · exact weighted_00_00_09_01
      · exact weighted_00_00_09_02
      · exact weighted_00_00_09_03
      · exact weighted_00_00_09_04
      · exact weighted_00_00_09_05
      · exact weighted_00_00_09_06
      · exact weighted_00_00_09_07
      · exact weighted_00_00_09_08
      · exact weighted_00_00_09_09
      · exact weighted_00_00_09_10
      · exact weighted_00_00_09_11
      · exact weighted_00_00_09_12
      · exact weighted_00_00_09_13
      · exact weighted_00_00_09_14
      · exact weighted_00_00_09_15
      · exact weighted_00_00_09_16
      · exact weighted_00_00_09_17
      · exact weighted_00_00_09_18
      · exact weighted_00_00_09_19
    _ = 462 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_09

end Paper7MomentGapNumeric
