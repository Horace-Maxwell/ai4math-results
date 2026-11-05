import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C07

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

theorem row_00_00_07_00 : b4RowContribution (![0, 0, 7, 7] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨7, by decide⟩⟩ = (![0, 0, 7, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_07
#print axioms Paper7MomentGapNumeric.row_00_00_07_00

theorem weighted_00_00_07_00 : b4RawGapContribution ![0, 0, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 0] = b4GapPatternWeight 0 7 0 * 0 :=
      b4GapContribution_from_row 0 0 7 0 0 row_00_00_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_00

theorem row_00_00_07_01 : b4RowContribution (![0, 0, 7, 8] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨8, by decide⟩⟩ = (![0, 0, 7, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_08
#print axioms Paper7MomentGapNumeric.row_00_00_07_01

theorem weighted_00_00_07_01 : b4RawGapContribution ![0, 0, 7, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 1] = b4GapPatternWeight 0 7 1 * 0 :=
      b4GapContribution_from_row 0 0 7 1 0 row_00_00_07_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_01

theorem row_00_00_07_02 : b4RowContribution (![0, 0, 7, 9] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨9, by decide⟩⟩ = (![0, 0, 7, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_09
#print axioms Paper7MomentGapNumeric.row_00_00_07_02

theorem weighted_00_00_07_02 : b4RawGapContribution ![0, 0, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 2] = b4GapPatternWeight 0 7 2 * 0 :=
      b4GapContribution_from_row 0 0 7 2 0 row_00_00_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_02

theorem row_00_00_07_03 : b4RowContribution (![0, 0, 7, 10] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨10, by decide⟩⟩ = (![0, 0, 7, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_10
#print axioms Paper7MomentGapNumeric.row_00_00_07_03

theorem weighted_00_00_07_03 : b4RawGapContribution ![0, 0, 7, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 3] = b4GapPatternWeight 0 7 3 * 0 :=
      b4GapContribution_from_row 0 0 7 3 0 row_00_00_07_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_03

theorem row_00_00_07_04 : b4RowContribution (![0, 0, 7, 11] : Fin 4 → ℕ) = 5 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨11, by decide⟩⟩ = (![0, 0, 7, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_11
#print axioms Paper7MomentGapNumeric.row_00_00_07_04

theorem weighted_00_00_07_04 : b4RawGapContribution ![0, 0, 7, 4] = 60 := by
  calc
    b4RawGapContribution ![0, 0, 7, 4] = b4GapPatternWeight 0 7 4 * 5 :=
      b4GapContribution_from_row 0 0 7 4 5 row_00_00_07_04
    _ = 60 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_04

theorem row_00_00_07_05 : b4RowContribution (![0, 0, 7, 12] : Fin 4 → ℕ) = 2 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨12, by decide⟩⟩ = (![0, 0, 7, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_12
#print axioms Paper7MomentGapNumeric.row_00_00_07_05

theorem weighted_00_00_07_05 : b4RawGapContribution ![0, 0, 7, 5] = 24 := by
  calc
    b4RawGapContribution ![0, 0, 7, 5] = b4GapPatternWeight 0 7 5 * 2 :=
      b4GapContribution_from_row 0 0 7 5 2 row_00_00_07_05
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_05

theorem row_00_00_07_06 : b4RowContribution (![0, 0, 7, 13] : Fin 4 → ℕ) = 12 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨13, by decide⟩⟩ = (![0, 0, 7, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_13
#print axioms Paper7MomentGapNumeric.row_00_00_07_06

theorem weighted_00_00_07_06 : b4RawGapContribution ![0, 0, 7, 6] = 144 := by
  calc
    b4RawGapContribution ![0, 0, 7, 6] = b4GapPatternWeight 0 7 6 * 12 :=
      b4GapContribution_from_row 0 0 7 6 12 row_00_00_07_06
    _ = 144 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_06

theorem row_00_00_07_07 : b4RowContribution (![0, 0, 7, 14] : Fin 4 → ℕ) = 8 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨14, by decide⟩⟩ = (![0, 0, 7, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_14
#print axioms Paper7MomentGapNumeric.row_00_00_07_07

theorem weighted_00_00_07_07 : b4RawGapContribution ![0, 0, 7, 7] = 96 := by
  calc
    b4RawGapContribution ![0, 0, 7, 7] = b4GapPatternWeight 0 7 7 * 8 :=
      b4GapContribution_from_row 0 0 7 7 8 row_00_00_07_07
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_07

theorem row_00_00_07_08 : b4RowContribution (![0, 0, 7, 15] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 7, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_15
#print axioms Paper7MomentGapNumeric.row_00_00_07_08

theorem weighted_00_00_07_08 : b4RawGapContribution ![0, 0, 7, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 8] = b4GapPatternWeight 0 7 8 * 0 :=
      b4GapContribution_from_row 0 0 7 8 0 row_00_00_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_08

theorem row_00_00_07_09 : b4RowContribution (![0, 0, 7, 16] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 7, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_16
#print axioms Paper7MomentGapNumeric.row_00_00_07_09

theorem weighted_00_00_07_09 : b4RawGapContribution ![0, 0, 7, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 9] = b4GapPatternWeight 0 7 9 * 0 :=
      b4GapContribution_from_row 0 0 7 9 0 row_00_00_07_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_09

theorem row_00_00_07_10 : b4RowContribution (![0, 0, 7, 17] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 7, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_17
#print axioms Paper7MomentGapNumeric.row_00_00_07_10

theorem weighted_00_00_07_10 : b4RawGapContribution ![0, 0, 7, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 10] = b4GapPatternWeight 0 7 10 * 0 :=
      b4GapContribution_from_row 0 0 7 10 0 row_00_00_07_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_10

theorem row_00_00_07_11 : b4RowContribution (![0, 0, 7, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 7, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_18
#print axioms Paper7MomentGapNumeric.row_00_00_07_11

theorem weighted_00_00_07_11 : b4RawGapContribution ![0, 0, 7, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 11] = b4GapPatternWeight 0 7 11 * 0 :=
      b4GapContribution_from_row 0 0 7 11 0 row_00_00_07_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_11

theorem row_00_00_07_12 : b4RowContribution (![0, 0, 7, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 7, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_19
#print axioms Paper7MomentGapNumeric.row_00_00_07_12

theorem weighted_00_00_07_12 : b4RawGapContribution ![0, 0, 7, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 12] = b4GapPatternWeight 0 7 12 * 0 :=
      b4GapContribution_from_row 0 0 7 12 0 row_00_00_07_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_12

theorem row_00_00_07_13 : b4RowContribution (![0, 0, 7, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 7, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_20
#print axioms Paper7MomentGapNumeric.row_00_00_07_13

theorem weighted_00_00_07_13 : b4RawGapContribution ![0, 0, 7, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 13] = b4GapPatternWeight 0 7 13 * 0 :=
      b4GapContribution_from_row 0 0 7 13 0 row_00_00_07_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_13

theorem row_00_00_07_14 : b4RowContribution (![0, 0, 7, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 7, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_21
#print axioms Paper7MomentGapNumeric.row_00_00_07_14

theorem weighted_00_00_07_14 : b4RawGapContribution ![0, 0, 7, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 14] = b4GapPatternWeight 0 7 14 * 0 :=
      b4GapContribution_from_row 0 0 7 14 0 row_00_00_07_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_14

theorem row_00_00_07_15 : b4RowContribution (![0, 0, 7, 22] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 7, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_22
#print axioms Paper7MomentGapNumeric.row_00_00_07_15

theorem weighted_00_00_07_15 : b4RawGapContribution ![0, 0, 7, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 15] = b4GapPatternWeight 0 7 15 * 0 :=
      b4GapContribution_from_row 0 0 7 15 0 row_00_00_07_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_15

theorem row_00_00_07_16 : b4RowContribution (![0, 0, 7, 23] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨23, by decide⟩⟩ = (![0, 0, 7, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_23
#print axioms Paper7MomentGapNumeric.row_00_00_07_16

theorem weighted_00_00_07_16 : b4RawGapContribution ![0, 0, 7, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 16] = b4GapPatternWeight 0 7 16 * 0 :=
      b4GapContribution_from_row 0 0 7 16 0 row_00_00_07_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_16

theorem row_00_00_07_17 : b4RowContribution (![0, 0, 7, 24] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨24, by decide⟩⟩ = (![0, 0, 7, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_24
#print axioms Paper7MomentGapNumeric.row_00_00_07_17

theorem weighted_00_00_07_17 : b4RawGapContribution ![0, 0, 7, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 17] = b4GapPatternWeight 0 7 17 * 0 :=
      b4GapContribution_from_row 0 0 7 17 0 row_00_00_07_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_17

theorem row_00_00_07_18 : b4RowContribution (![0, 0, 7, 25] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨25, by decide⟩⟩ = (![0, 0, 7, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_25
#print axioms Paper7MomentGapNumeric.row_00_00_07_18

theorem weighted_00_00_07_18 : b4RawGapContribution ![0, 0, 7, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 18] = b4GapPatternWeight 0 7 18 * 0 :=
      b4GapContribution_from_row 0 0 7 18 0 row_00_00_07_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_18

theorem row_00_00_07_19 : b4RowContribution (![0, 0, 7, 26] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨26, by decide⟩⟩ = (![0, 0, 7, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_26
#print axioms Paper7MomentGapNumeric.row_00_00_07_19

theorem weighted_00_00_07_19 : b4RawGapContribution ![0, 0, 7, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 19] = b4GapPatternWeight 0 7 19 * 0 :=
      b4GapContribution_from_row 0 0 7 19 0 row_00_00_07_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_19

theorem row_00_00_07_20 : b4RowContribution (![0, 0, 7, 27] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨27, by decide⟩⟩ = (![0, 0, 7, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_27
#print axioms Paper7MomentGapNumeric.row_00_00_07_20

theorem weighted_00_00_07_20 : b4RawGapContribution ![0, 0, 7, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 20] = b4GapPatternWeight 0 7 20 * 0 :=
      b4GapContribution_from_row 0 0 7 20 0 row_00_00_07_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_20

theorem row_00_00_07_21 : b4RowContribution (![0, 0, 7, 28] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨28, by decide⟩⟩ = (![0, 0, 7, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_28
#print axioms Paper7MomentGapNumeric.row_00_00_07_21

theorem weighted_00_00_07_21 : b4RawGapContribution ![0, 0, 7, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 21] = b4GapPatternWeight 0 7 21 * 0 :=
      b4GapContribution_from_row 0 0 7 21 0 row_00_00_07_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_21

theorem row_00_00_07_22 : b4RowContribution (![0, 0, 7, 29] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨29, by decide⟩⟩ = (![0, 0, 7, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_29
#print axioms Paper7MomentGapNumeric.row_00_00_07_22

theorem weighted_00_00_07_22 : b4RawGapContribution ![0, 0, 7, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 22] = b4GapPatternWeight 0 7 22 * 0 :=
      b4GapContribution_from_row 0 0 7 22 0 row_00_00_07_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_22

theorem row_00_00_07_23 : b4RowContribution (![0, 0, 7, 30] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨7, by decide⟩, ⟨30, by decide⟩⟩ = (![0, 0, 7, 30] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_07_30
#print axioms Paper7MomentGapNumeric.row_00_00_07_23

theorem weighted_00_00_07_23 : b4RawGapContribution ![0, 0, 7, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 7, 23] = b4GapPatternWeight 0 7 23 * 0 :=
      b4GapContribution_from_row 0 0 7 23 0 row_00_00_07_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_07_23

def dvalues_00_00_07 : Fin 24 → ℕ := ![0, 0, 0, 0, 60, 24, 144, 96, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_07

theorem dblock_00_00_07 : b4GapPatternDBlock 0 0 7 = 324 := by
  calc
    b4GapPatternDBlock 0 0 7 = ∑ d : Fin 24, dvalues_00_00_07 d := by
      apply b4GapDBlock_of_rows 0 0 7 dvalues_00_00_07
      intro d
      fin_cases d
      · exact weighted_00_00_07_00
      · exact weighted_00_00_07_01
      · exact weighted_00_00_07_02
      · exact weighted_00_00_07_03
      · exact weighted_00_00_07_04
      · exact weighted_00_00_07_05
      · exact weighted_00_00_07_06
      · exact weighted_00_00_07_07
      · exact weighted_00_00_07_08
      · exact weighted_00_00_07_09
      · exact weighted_00_00_07_10
      · exact weighted_00_00_07_11
      · exact weighted_00_00_07_12
      · exact weighted_00_00_07_13
      · exact weighted_00_00_07_14
      · exact weighted_00_00_07_15
      · exact weighted_00_00_07_16
      · exact weighted_00_00_07_17
      · exact weighted_00_00_07_18
      · exact weighted_00_00_07_19
      · exact weighted_00_00_07_20
      · exact weighted_00_00_07_21
      · exact weighted_00_00_07_22
      · exact weighted_00_00_07_23
    _ = 324 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_07

end Paper7MomentGapNumeric
