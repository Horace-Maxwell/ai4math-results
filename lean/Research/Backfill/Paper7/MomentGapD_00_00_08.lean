import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C08

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

theorem row_00_00_08_00 : b4RowContribution (![0, 0, 8, 8] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨8, by decide⟩⟩ = (![0, 0, 8, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_08
#print axioms Paper7MomentGapNumeric.row_00_00_08_00

theorem weighted_00_00_08_00 : b4RawGapContribution ![0, 0, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 0] = b4GapPatternWeight 0 8 0 * 0 :=
      b4GapContribution_from_row 0 0 8 0 0 row_00_00_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_00

theorem row_00_00_08_01 : b4RowContribution (![0, 0, 8, 9] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨9, by decide⟩⟩ = (![0, 0, 8, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_09
#print axioms Paper7MomentGapNumeric.row_00_00_08_01

theorem weighted_00_00_08_01 : b4RawGapContribution ![0, 0, 8, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 1] = b4GapPatternWeight 0 8 1 * 0 :=
      b4GapContribution_from_row 0 0 8 1 0 row_00_00_08_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_01

theorem row_00_00_08_02 : b4RowContribution (![0, 0, 8, 10] : Fin 4 → ℕ) = 2 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨10, by decide⟩⟩ = (![0, 0, 8, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_10
#print axioms Paper7MomentGapNumeric.row_00_00_08_02

theorem weighted_00_00_08_02 : b4RawGapContribution ![0, 0, 8, 2] = 24 := by
  calc
    b4RawGapContribution ![0, 0, 8, 2] = b4GapPatternWeight 0 8 2 * 2 :=
      b4GapContribution_from_row 0 0 8 2 2 row_00_00_08_02
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_02

theorem row_00_00_08_03 : b4RowContribution (![0, 0, 8, 11] : Fin 4 → ℕ) = 6 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨11, by decide⟩⟩ = (![0, 0, 8, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_11
#print axioms Paper7MomentGapNumeric.row_00_00_08_03

theorem weighted_00_00_08_03 : b4RawGapContribution ![0, 0, 8, 3] = 72 := by
  calc
    b4RawGapContribution ![0, 0, 8, 3] = b4GapPatternWeight 0 8 3 * 6 :=
      b4GapContribution_from_row 0 0 8 3 6 row_00_00_08_03
    _ = 72 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_03

theorem row_00_00_08_04 : b4RowContribution (![0, 0, 8, 12] : Fin 4 → ℕ) = 5 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨12, by decide⟩⟩ = (![0, 0, 8, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_12
#print axioms Paper7MomentGapNumeric.row_00_00_08_04

theorem weighted_00_00_08_04 : b4RawGapContribution ![0, 0, 8, 4] = 60 := by
  calc
    b4RawGapContribution ![0, 0, 8, 4] = b4GapPatternWeight 0 8 4 * 5 :=
      b4GapContribution_from_row 0 0 8 4 5 row_00_00_08_04
    _ = 60 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_04

theorem row_00_00_08_05 : b4RowContribution (![0, 0, 8, 13] : Fin 4 → ℕ) = 20 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨13, by decide⟩⟩ = (![0, 0, 8, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_13
#print axioms Paper7MomentGapNumeric.row_00_00_08_05

theorem weighted_00_00_08_05 : b4RawGapContribution ![0, 0, 8, 5] = 240 := by
  calc
    b4RawGapContribution ![0, 0, 8, 5] = b4GapPatternWeight 0 8 5 * 20 :=
      b4GapContribution_from_row 0 0 8 5 20 row_00_00_08_05
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_05

theorem row_00_00_08_06 : b4RowContribution (![0, 0, 8, 14] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨14, by decide⟩⟩ = (![0, 0, 8, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_14
#print axioms Paper7MomentGapNumeric.row_00_00_08_06

theorem weighted_00_00_08_06 : b4RawGapContribution ![0, 0, 8, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 6] = b4GapPatternWeight 0 8 6 * 0 :=
      b4GapContribution_from_row 0 0 8 6 0 row_00_00_08_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_06

theorem row_00_00_08_07 : b4RowContribution (![0, 0, 8, 15] : Fin 4 → ℕ) = 17 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 8, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_15
#print axioms Paper7MomentGapNumeric.row_00_00_08_07

theorem weighted_00_00_08_07 : b4RawGapContribution ![0, 0, 8, 7] = 204 := by
  calc
    b4RawGapContribution ![0, 0, 8, 7] = b4GapPatternWeight 0 8 7 * 17 :=
      b4GapContribution_from_row 0 0 8 7 17 row_00_00_08_07
    _ = 204 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_07

theorem row_00_00_08_08 : b4RowContribution (![0, 0, 8, 16] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 8, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_16
#print axioms Paper7MomentGapNumeric.row_00_00_08_08

theorem weighted_00_00_08_08 : b4RawGapContribution ![0, 0, 8, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 8] = b4GapPatternWeight 0 8 8 * 0 :=
      b4GapContribution_from_row 0 0 8 8 0 row_00_00_08_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_08

theorem row_00_00_08_09 : b4RowContribution (![0, 0, 8, 17] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 8, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_17
#print axioms Paper7MomentGapNumeric.row_00_00_08_09

theorem weighted_00_00_08_09 : b4RawGapContribution ![0, 0, 8, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 9] = b4GapPatternWeight 0 8 9 * 0 :=
      b4GapContribution_from_row 0 0 8 9 0 row_00_00_08_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_09

theorem row_00_00_08_10 : b4RowContribution (![0, 0, 8, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 8, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_18
#print axioms Paper7MomentGapNumeric.row_00_00_08_10

theorem weighted_00_00_08_10 : b4RawGapContribution ![0, 0, 8, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 10] = b4GapPatternWeight 0 8 10 * 0 :=
      b4GapContribution_from_row 0 0 8 10 0 row_00_00_08_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_10

theorem row_00_00_08_11 : b4RowContribution (![0, 0, 8, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 8, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_19
#print axioms Paper7MomentGapNumeric.row_00_00_08_11

theorem weighted_00_00_08_11 : b4RawGapContribution ![0, 0, 8, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 11] = b4GapPatternWeight 0 8 11 * 0 :=
      b4GapContribution_from_row 0 0 8 11 0 row_00_00_08_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_11

theorem row_00_00_08_12 : b4RowContribution (![0, 0, 8, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 8, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_20
#print axioms Paper7MomentGapNumeric.row_00_00_08_12

theorem weighted_00_00_08_12 : b4RawGapContribution ![0, 0, 8, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 12] = b4GapPatternWeight 0 8 12 * 0 :=
      b4GapContribution_from_row 0 0 8 12 0 row_00_00_08_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_12

theorem row_00_00_08_13 : b4RowContribution (![0, 0, 8, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 8, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_21
#print axioms Paper7MomentGapNumeric.row_00_00_08_13

theorem weighted_00_00_08_13 : b4RawGapContribution ![0, 0, 8, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 13] = b4GapPatternWeight 0 8 13 * 0 :=
      b4GapContribution_from_row 0 0 8 13 0 row_00_00_08_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_13

theorem row_00_00_08_14 : b4RowContribution (![0, 0, 8, 22] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 8, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_22
#print axioms Paper7MomentGapNumeric.row_00_00_08_14

theorem weighted_00_00_08_14 : b4RawGapContribution ![0, 0, 8, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 14] = b4GapPatternWeight 0 8 14 * 0 :=
      b4GapContribution_from_row 0 0 8 14 0 row_00_00_08_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_14

theorem row_00_00_08_15 : b4RowContribution (![0, 0, 8, 23] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨23, by decide⟩⟩ = (![0, 0, 8, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_23
#print axioms Paper7MomentGapNumeric.row_00_00_08_15

theorem weighted_00_00_08_15 : b4RawGapContribution ![0, 0, 8, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 15] = b4GapPatternWeight 0 8 15 * 0 :=
      b4GapContribution_from_row 0 0 8 15 0 row_00_00_08_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_15

theorem row_00_00_08_16 : b4RowContribution (![0, 0, 8, 24] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨24, by decide⟩⟩ = (![0, 0, 8, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_24
#print axioms Paper7MomentGapNumeric.row_00_00_08_16

theorem weighted_00_00_08_16 : b4RawGapContribution ![0, 0, 8, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 16] = b4GapPatternWeight 0 8 16 * 0 :=
      b4GapContribution_from_row 0 0 8 16 0 row_00_00_08_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_16

theorem row_00_00_08_17 : b4RowContribution (![0, 0, 8, 25] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨25, by decide⟩⟩ = (![0, 0, 8, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_25
#print axioms Paper7MomentGapNumeric.row_00_00_08_17

theorem weighted_00_00_08_17 : b4RawGapContribution ![0, 0, 8, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 17] = b4GapPatternWeight 0 8 17 * 0 :=
      b4GapContribution_from_row 0 0 8 17 0 row_00_00_08_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_17

theorem row_00_00_08_18 : b4RowContribution (![0, 0, 8, 26] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨26, by decide⟩⟩ = (![0, 0, 8, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_26
#print axioms Paper7MomentGapNumeric.row_00_00_08_18

theorem weighted_00_00_08_18 : b4RawGapContribution ![0, 0, 8, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 18] = b4GapPatternWeight 0 8 18 * 0 :=
      b4GapContribution_from_row 0 0 8 18 0 row_00_00_08_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_18

theorem row_00_00_08_19 : b4RowContribution (![0, 0, 8, 27] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨27, by decide⟩⟩ = (![0, 0, 8, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_27
#print axioms Paper7MomentGapNumeric.row_00_00_08_19

theorem weighted_00_00_08_19 : b4RawGapContribution ![0, 0, 8, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 19] = b4GapPatternWeight 0 8 19 * 0 :=
      b4GapContribution_from_row 0 0 8 19 0 row_00_00_08_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_19

theorem row_00_00_08_20 : b4RowContribution (![0, 0, 8, 28] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨28, by decide⟩⟩ = (![0, 0, 8, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_28
#print axioms Paper7MomentGapNumeric.row_00_00_08_20

theorem weighted_00_00_08_20 : b4RawGapContribution ![0, 0, 8, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 20] = b4GapPatternWeight 0 8 20 * 0 :=
      b4GapContribution_from_row 0 0 8 20 0 row_00_00_08_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_20

theorem row_00_00_08_21 : b4RowContribution (![0, 0, 8, 29] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨8, by decide⟩, ⟨29, by decide⟩⟩ = (![0, 0, 8, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_08_29
#print axioms Paper7MomentGapNumeric.row_00_00_08_21

theorem weighted_00_00_08_21 : b4RawGapContribution ![0, 0, 8, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 8, 21] = b4GapPatternWeight 0 8 21 * 0 :=
      b4GapContribution_from_row 0 0 8 21 0 row_00_00_08_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_08_21

def dvalues_00_00_08 : Fin 22 → ℕ := ![0, 0, 24, 72, 60, 240, 0, 204, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_08

theorem dblock_00_00_08 : b4GapPatternDBlock 0 0 8 = 600 := by
  calc
    b4GapPatternDBlock 0 0 8 = ∑ d : Fin 22, dvalues_00_00_08 d := by
      apply b4GapDBlock_of_rows 0 0 8 dvalues_00_00_08
      intro d
      fin_cases d
      · exact weighted_00_00_08_00
      · exact weighted_00_00_08_01
      · exact weighted_00_00_08_02
      · exact weighted_00_00_08_03
      · exact weighted_00_00_08_04
      · exact weighted_00_00_08_05
      · exact weighted_00_00_08_06
      · exact weighted_00_00_08_07
      · exact weighted_00_00_08_08
      · exact weighted_00_00_08_09
      · exact weighted_00_00_08_10
      · exact weighted_00_00_08_11
      · exact weighted_00_00_08_12
      · exact weighted_00_00_08_13
      · exact weighted_00_00_08_14
      · exact weighted_00_00_08_15
      · exact weighted_00_00_08_16
      · exact weighted_00_00_08_17
      · exact weighted_00_00_08_18
      · exact weighted_00_00_08_19
      · exact weighted_00_00_08_20
      · exact weighted_00_00_08_21
    _ = 600 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_08

end Paper7MomentGapNumeric
