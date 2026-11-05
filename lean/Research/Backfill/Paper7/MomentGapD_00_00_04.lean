import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C04

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

theorem row_00_00_04_00 : b4RowContribution (![0, 0, 4, 4] : Fin 4 → ℕ) = 1 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨4, by decide⟩⟩ = (![0, 0, 4, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_04
#print axioms Paper7MomentGapNumeric.row_00_00_04_00

theorem weighted_00_00_04_00 : b4RawGapContribution ![0, 0, 4, 0] = 6 := by
  calc
    b4RawGapContribution ![0, 0, 4, 0] = b4GapPatternWeight 0 4 0 * 1 :=
      b4GapContribution_from_row 0 0 4 0 1 row_00_00_04_00
    _ = 6 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_00

theorem row_00_00_04_01 : b4RowContribution (![0, 0, 4, 5] : Fin 4 → ℕ) = 5 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨5, by decide⟩⟩ = (![0, 0, 4, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_05
#print axioms Paper7MomentGapNumeric.row_00_00_04_01

theorem weighted_00_00_04_01 : b4RawGapContribution ![0, 0, 4, 1] = 60 := by
  calc
    b4RawGapContribution ![0, 0, 4, 1] = b4GapPatternWeight 0 4 1 * 5 :=
      b4GapContribution_from_row 0 0 4 1 5 row_00_00_04_01
    _ = 60 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_01

theorem row_00_00_04_02 : b4RowContribution (![0, 0, 4, 6] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨6, by decide⟩⟩ = (![0, 0, 4, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_06
#print axioms Paper7MomentGapNumeric.row_00_00_04_02

theorem weighted_00_00_04_02 : b4RawGapContribution ![0, 0, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 2] = b4GapPatternWeight 0 4 2 * 0 :=
      b4GapContribution_from_row 0 0 4 2 0 row_00_00_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_02

theorem row_00_00_04_03 : b4RowContribution (![0, 0, 4, 7] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨7, by decide⟩⟩ = (![0, 0, 4, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_07
#print axioms Paper7MomentGapNumeric.row_00_00_04_03

theorem weighted_00_00_04_03 : b4RawGapContribution ![0, 0, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 3] = b4GapPatternWeight 0 4 3 * 0 :=
      b4GapContribution_from_row 0 0 4 3 0 row_00_00_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_03

theorem row_00_00_04_04 : b4RowContribution (![0, 0, 4, 8] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨8, by decide⟩⟩ = (![0, 0, 4, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_08
#print axioms Paper7MomentGapNumeric.row_00_00_04_04

theorem weighted_00_00_04_04 : b4RawGapContribution ![0, 0, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 4] = b4GapPatternWeight 0 4 4 * 0 :=
      b4GapContribution_from_row 0 0 4 4 0 row_00_00_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_04

theorem row_00_00_04_05 : b4RowContribution (![0, 0, 4, 9] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨9, by decide⟩⟩ = (![0, 0, 4, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_09
#print axioms Paper7MomentGapNumeric.row_00_00_04_05

theorem weighted_00_00_04_05 : b4RawGapContribution ![0, 0, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 5] = b4GapPatternWeight 0 4 5 * 0 :=
      b4GapContribution_from_row 0 0 4 5 0 row_00_00_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_05

theorem row_00_00_04_06 : b4RowContribution (![0, 0, 4, 10] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨10, by decide⟩⟩ = (![0, 0, 4, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_10
#print axioms Paper7MomentGapNumeric.row_00_00_04_06

theorem weighted_00_00_04_06 : b4RawGapContribution ![0, 0, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 6] = b4GapPatternWeight 0 4 6 * 0 :=
      b4GapContribution_from_row 0 0 4 6 0 row_00_00_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_06

theorem row_00_00_04_07 : b4RowContribution (![0, 0, 4, 11] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨11, by decide⟩⟩ = (![0, 0, 4, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_11
#print axioms Paper7MomentGapNumeric.row_00_00_04_07

theorem weighted_00_00_04_07 : b4RawGapContribution ![0, 0, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 7] = b4GapPatternWeight 0 4 7 * 0 :=
      b4GapContribution_from_row 0 0 4 7 0 row_00_00_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_07

theorem row_00_00_04_08 : b4RowContribution (![0, 0, 4, 12] : Fin 4 → ℕ) = 1 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨12, by decide⟩⟩ = (![0, 0, 4, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_12
#print axioms Paper7MomentGapNumeric.row_00_00_04_08

theorem weighted_00_00_04_08 : b4RawGapContribution ![0, 0, 4, 8] = 12 := by
  calc
    b4RawGapContribution ![0, 0, 4, 8] = b4GapPatternWeight 0 4 8 * 1 :=
      b4GapContribution_from_row 0 0 4 8 1 row_00_00_04_08
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_08

theorem row_00_00_04_09 : b4RowContribution (![0, 0, 4, 13] : Fin 4 → ℕ) = 5 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨13, by decide⟩⟩ = (![0, 0, 4, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_13
#print axioms Paper7MomentGapNumeric.row_00_00_04_09

theorem weighted_00_00_04_09 : b4RawGapContribution ![0, 0, 4, 9] = 60 := by
  calc
    b4RawGapContribution ![0, 0, 4, 9] = b4GapPatternWeight 0 4 9 * 5 :=
      b4GapContribution_from_row 0 0 4 9 5 row_00_00_04_09
    _ = 60 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_09

theorem row_00_00_04_10 : b4RowContribution (![0, 0, 4, 14] : Fin 4 → ℕ) = 2 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨14, by decide⟩⟩ = (![0, 0, 4, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_14
#print axioms Paper7MomentGapNumeric.row_00_00_04_10

theorem weighted_00_00_04_10 : b4RawGapContribution ![0, 0, 4, 10] = 24 := by
  calc
    b4RawGapContribution ![0, 0, 4, 10] = b4GapPatternWeight 0 4 10 * 2 :=
      b4GapContribution_from_row 0 0 4 10 2 row_00_00_04_10
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_10

theorem row_00_00_04_11 : b4RowContribution (![0, 0, 4, 15] : Fin 4 → ℕ) = 10 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 4, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_15
#print axioms Paper7MomentGapNumeric.row_00_00_04_11

theorem weighted_00_00_04_11 : b4RawGapContribution ![0, 0, 4, 11] = 120 := by
  calc
    b4RawGapContribution ![0, 0, 4, 11] = b4GapPatternWeight 0 4 11 * 10 :=
      b4GapContribution_from_row 0 0 4 11 10 row_00_00_04_11
    _ = 120 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_11

theorem row_00_00_04_12 : b4RowContribution (![0, 0, 4, 16] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 4, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_16
#print axioms Paper7MomentGapNumeric.row_00_00_04_12

theorem weighted_00_00_04_12 : b4RawGapContribution ![0, 0, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 12] = b4GapPatternWeight 0 4 12 * 0 :=
      b4GapContribution_from_row 0 0 4 12 0 row_00_00_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_12

theorem row_00_00_04_13 : b4RowContribution (![0, 0, 4, 17] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 4, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_17
#print axioms Paper7MomentGapNumeric.row_00_00_04_13

theorem weighted_00_00_04_13 : b4RawGapContribution ![0, 0, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 13] = b4GapPatternWeight 0 4 13 * 0 :=
      b4GapContribution_from_row 0 0 4 13 0 row_00_00_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_13

theorem row_00_00_04_14 : b4RowContribution (![0, 0, 4, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 4, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_18
#print axioms Paper7MomentGapNumeric.row_00_00_04_14

theorem weighted_00_00_04_14 : b4RawGapContribution ![0, 0, 4, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 14] = b4GapPatternWeight 0 4 14 * 0 :=
      b4GapContribution_from_row 0 0 4 14 0 row_00_00_04_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_14

theorem row_00_00_04_15 : b4RowContribution (![0, 0, 4, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 4, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_19
#print axioms Paper7MomentGapNumeric.row_00_00_04_15

theorem weighted_00_00_04_15 : b4RawGapContribution ![0, 0, 4, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 15] = b4GapPatternWeight 0 4 15 * 0 :=
      b4GapContribution_from_row 0 0 4 15 0 row_00_00_04_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_15

theorem row_00_00_04_16 : b4RowContribution (![0, 0, 4, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 4, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_20
#print axioms Paper7MomentGapNumeric.row_00_00_04_16

theorem weighted_00_00_04_16 : b4RawGapContribution ![0, 0, 4, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 16] = b4GapPatternWeight 0 4 16 * 0 :=
      b4GapContribution_from_row 0 0 4 16 0 row_00_00_04_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_16

theorem row_00_00_04_17 : b4RowContribution (![0, 0, 4, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 4, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_21
#print axioms Paper7MomentGapNumeric.row_00_00_04_17

theorem weighted_00_00_04_17 : b4RawGapContribution ![0, 0, 4, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 17] = b4GapPatternWeight 0 4 17 * 0 :=
      b4GapContribution_from_row 0 0 4 17 0 row_00_00_04_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_17

theorem row_00_00_04_18 : b4RowContribution (![0, 0, 4, 22] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 4, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_22
#print axioms Paper7MomentGapNumeric.row_00_00_04_18

theorem weighted_00_00_04_18 : b4RawGapContribution ![0, 0, 4, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 18] = b4GapPatternWeight 0 4 18 * 0 :=
      b4GapContribution_from_row 0 0 4 18 0 row_00_00_04_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_18

theorem row_00_00_04_19 : b4RowContribution (![0, 0, 4, 23] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨23, by decide⟩⟩ = (![0, 0, 4, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_23
#print axioms Paper7MomentGapNumeric.row_00_00_04_19

theorem weighted_00_00_04_19 : b4RawGapContribution ![0, 0, 4, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 19] = b4GapPatternWeight 0 4 19 * 0 :=
      b4GapContribution_from_row 0 0 4 19 0 row_00_00_04_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_19

theorem row_00_00_04_20 : b4RowContribution (![0, 0, 4, 24] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨24, by decide⟩⟩ = (![0, 0, 4, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_24
#print axioms Paper7MomentGapNumeric.row_00_00_04_20

theorem weighted_00_00_04_20 : b4RawGapContribution ![0, 0, 4, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 20] = b4GapPatternWeight 0 4 20 * 0 :=
      b4GapContribution_from_row 0 0 4 20 0 row_00_00_04_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_20

theorem row_00_00_04_21 : b4RowContribution (![0, 0, 4, 25] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨25, by decide⟩⟩ = (![0, 0, 4, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_25
#print axioms Paper7MomentGapNumeric.row_00_00_04_21

theorem weighted_00_00_04_21 : b4RawGapContribution ![0, 0, 4, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 21] = b4GapPatternWeight 0 4 21 * 0 :=
      b4GapContribution_from_row 0 0 4 21 0 row_00_00_04_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_21

theorem row_00_00_04_22 : b4RowContribution (![0, 0, 4, 26] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨26, by decide⟩⟩ = (![0, 0, 4, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_26
#print axioms Paper7MomentGapNumeric.row_00_00_04_22

theorem weighted_00_00_04_22 : b4RawGapContribution ![0, 0, 4, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 22] = b4GapPatternWeight 0 4 22 * 0 :=
      b4GapContribution_from_row 0 0 4 22 0 row_00_00_04_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_22

theorem row_00_00_04_23 : b4RowContribution (![0, 0, 4, 27] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨27, by decide⟩⟩ = (![0, 0, 4, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_27
#print axioms Paper7MomentGapNumeric.row_00_00_04_23

theorem weighted_00_00_04_23 : b4RawGapContribution ![0, 0, 4, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 23] = b4GapPatternWeight 0 4 23 * 0 :=
      b4GapContribution_from_row 0 0 4 23 0 row_00_00_04_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_23

theorem row_00_00_04_24 : b4RowContribution (![0, 0, 4, 28] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨28, by decide⟩⟩ = (![0, 0, 4, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_28
#print axioms Paper7MomentGapNumeric.row_00_00_04_24

theorem weighted_00_00_04_24 : b4RawGapContribution ![0, 0, 4, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 24] = b4GapPatternWeight 0 4 24 * 0 :=
      b4GapContribution_from_row 0 0 4 24 0 row_00_00_04_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_24

theorem row_00_00_04_25 : b4RowContribution (![0, 0, 4, 29] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨29, by decide⟩⟩ = (![0, 0, 4, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_29
#print axioms Paper7MomentGapNumeric.row_00_00_04_25

theorem weighted_00_00_04_25 : b4RawGapContribution ![0, 0, 4, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 25] = b4GapPatternWeight 0 4 25 * 0 :=
      b4GapContribution_from_row 0 0 4 25 0 row_00_00_04_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_25

theorem row_00_00_04_26 : b4RowContribution (![0, 0, 4, 30] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨30, by decide⟩⟩ = (![0, 0, 4, 30] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_30
#print axioms Paper7MomentGapNumeric.row_00_00_04_26

theorem weighted_00_00_04_26 : b4RawGapContribution ![0, 0, 4, 26] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 26] = b4GapPatternWeight 0 4 26 * 0 :=
      b4GapContribution_from_row 0 0 4 26 0 row_00_00_04_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_26

theorem row_00_00_04_27 : b4RowContribution (![0, 0, 4, 31] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨31, by decide⟩⟩ = (![0, 0, 4, 31] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_31
#print axioms Paper7MomentGapNumeric.row_00_00_04_27

theorem weighted_00_00_04_27 : b4RawGapContribution ![0, 0, 4, 27] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 27] = b4GapPatternWeight 0 4 27 * 0 :=
      b4GapContribution_from_row 0 0 4 27 0 row_00_00_04_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_27

theorem row_00_00_04_28 : b4RowContribution (![0, 0, 4, 32] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨32, by decide⟩⟩ = (![0, 0, 4, 32] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_32
#print axioms Paper7MomentGapNumeric.row_00_00_04_28

theorem weighted_00_00_04_28 : b4RawGapContribution ![0, 0, 4, 28] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 28] = b4GapPatternWeight 0 4 28 * 0 :=
      b4GapContribution_from_row 0 0 4 28 0 row_00_00_04_28
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_28

theorem row_00_00_04_29 : b4RowContribution (![0, 0, 4, 33] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨4, by decide⟩, ⟨33, by decide⟩⟩ = (![0, 0, 4, 33] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_04_33
#print axioms Paper7MomentGapNumeric.row_00_00_04_29

theorem weighted_00_00_04_29 : b4RawGapContribution ![0, 0, 4, 29] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 4, 29] = b4GapPatternWeight 0 4 29 * 0 :=
      b4GapContribution_from_row 0 0 4 29 0 row_00_00_04_29
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_04_29

def dvalues_00_00_04 : Fin 30 → ℕ := ![6, 60, 0, 0, 0, 0, 0, 0, 12, 60, 24, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_04

theorem dblock_00_00_04 : b4GapPatternDBlock 0 0 4 = 282 := by
  calc
    b4GapPatternDBlock 0 0 4 = ∑ d : Fin 30, dvalues_00_00_04 d := by
      apply b4GapDBlock_of_rows 0 0 4 dvalues_00_00_04
      intro d
      fin_cases d
      · exact weighted_00_00_04_00
      · exact weighted_00_00_04_01
      · exact weighted_00_00_04_02
      · exact weighted_00_00_04_03
      · exact weighted_00_00_04_04
      · exact weighted_00_00_04_05
      · exact weighted_00_00_04_06
      · exact weighted_00_00_04_07
      · exact weighted_00_00_04_08
      · exact weighted_00_00_04_09
      · exact weighted_00_00_04_10
      · exact weighted_00_00_04_11
      · exact weighted_00_00_04_12
      · exact weighted_00_00_04_13
      · exact weighted_00_00_04_14
      · exact weighted_00_00_04_15
      · exact weighted_00_00_04_16
      · exact weighted_00_00_04_17
      · exact weighted_00_00_04_18
      · exact weighted_00_00_04_19
      · exact weighted_00_00_04_20
      · exact weighted_00_00_04_21
      · exact weighted_00_00_04_22
      · exact weighted_00_00_04_23
      · exact weighted_00_00_04_24
      · exact weighted_00_00_04_25
      · exact weighted_00_00_04_26
      · exact weighted_00_00_04_27
      · exact weighted_00_00_04_28
      · exact weighted_00_00_04_29
    _ = 282 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_04

end Paper7MomentGapNumeric
