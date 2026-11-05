import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C02

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

theorem row_00_00_02_00 : b4RowContribution (![0, 0, 2, 2] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨2, by decide⟩⟩ = (![0, 0, 2, 2] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_02
#print axioms Paper7MomentGapNumeric.row_00_00_02_00

theorem weighted_00_00_02_00 : b4RawGapContribution ![0, 0, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 0] = b4GapPatternWeight 0 2 0 * 0 :=
      b4GapContribution_from_row 0 0 2 0 0 row_00_00_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_00

theorem row_00_00_02_01 : b4RowContribution (![0, 0, 2, 3] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨3, by decide⟩⟩ = (![0, 0, 2, 3] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_03
#print axioms Paper7MomentGapNumeric.row_00_00_02_01

theorem weighted_00_00_02_01 : b4RawGapContribution ![0, 0, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 1] = b4GapPatternWeight 0 2 1 * 0 :=
      b4GapContribution_from_row 0 0 2 1 0 row_00_00_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_01

theorem row_00_00_02_02 : b4RowContribution (![0, 0, 2, 4] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨4, by decide⟩⟩ = (![0, 0, 2, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_04
#print axioms Paper7MomentGapNumeric.row_00_00_02_02

theorem weighted_00_00_02_02 : b4RawGapContribution ![0, 0, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 2] = b4GapPatternWeight 0 2 2 * 0 :=
      b4GapContribution_from_row 0 0 2 2 0 row_00_00_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_02

theorem row_00_00_02_03 : b4RowContribution (![0, 0, 2, 5] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨5, by decide⟩⟩ = (![0, 0, 2, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_05
#print axioms Paper7MomentGapNumeric.row_00_00_02_03

theorem weighted_00_00_02_03 : b4RawGapContribution ![0, 0, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 3] = b4GapPatternWeight 0 2 3 * 0 :=
      b4GapContribution_from_row 0 0 2 3 0 row_00_00_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_03

theorem row_00_00_02_04 : b4RowContribution (![0, 0, 2, 6] : Fin 4 → ℕ) = 3 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨6, by decide⟩⟩ = (![0, 0, 2, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_06
#print axioms Paper7MomentGapNumeric.row_00_00_02_04

theorem weighted_00_00_02_04 : b4RawGapContribution ![0, 0, 2, 4] = 36 := by
  calc
    b4RawGapContribution ![0, 0, 2, 4] = b4GapPatternWeight 0 2 4 * 3 :=
      b4GapContribution_from_row 0 0 2 4 3 row_00_00_02_04
    _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_04

theorem row_00_00_02_05 : b4RowContribution (![0, 0, 2, 7] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨7, by decide⟩⟩ = (![0, 0, 2, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_07
#print axioms Paper7MomentGapNumeric.row_00_00_02_05

theorem weighted_00_00_02_05 : b4RawGapContribution ![0, 0, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 5] = b4GapPatternWeight 0 2 5 * 0 :=
      b4GapContribution_from_row 0 0 2 5 0 row_00_00_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_05

theorem row_00_00_02_06 : b4RowContribution (![0, 0, 2, 8] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨8, by decide⟩⟩ = (![0, 0, 2, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_08
#print axioms Paper7MomentGapNumeric.row_00_00_02_06

theorem weighted_00_00_02_06 : b4RawGapContribution ![0, 0, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 6] = b4GapPatternWeight 0 2 6 * 0 :=
      b4GapContribution_from_row 0 0 2 6 0 row_00_00_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_06

theorem row_00_00_02_07 : b4RowContribution (![0, 0, 2, 9] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨9, by decide⟩⟩ = (![0, 0, 2, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_09
#print axioms Paper7MomentGapNumeric.row_00_00_02_07

theorem weighted_00_00_02_07 : b4RawGapContribution ![0, 0, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 7] = b4GapPatternWeight 0 2 7 * 0 :=
      b4GapContribution_from_row 0 0 2 7 0 row_00_00_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_07

theorem row_00_00_02_08 : b4RowContribution (![0, 0, 2, 10] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨10, by decide⟩⟩ = (![0, 0, 2, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_10
#print axioms Paper7MomentGapNumeric.row_00_00_02_08

theorem weighted_00_00_02_08 : b4RawGapContribution ![0, 0, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 8] = b4GapPatternWeight 0 2 8 * 0 :=
      b4GapContribution_from_row 0 0 2 8 0 row_00_00_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_08

theorem row_00_00_02_09 : b4RowContribution (![0, 0, 2, 11] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨11, by decide⟩⟩ = (![0, 0, 2, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_11
#print axioms Paper7MomentGapNumeric.row_00_00_02_09

theorem weighted_00_00_02_09 : b4RawGapContribution ![0, 0, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 9] = b4GapPatternWeight 0 2 9 * 0 :=
      b4GapContribution_from_row 0 0 2 9 0 row_00_00_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_09

theorem row_00_00_02_10 : b4RowContribution (![0, 0, 2, 12] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨12, by decide⟩⟩ = (![0, 0, 2, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_12
#print axioms Paper7MomentGapNumeric.row_00_00_02_10

theorem weighted_00_00_02_10 : b4RawGapContribution ![0, 0, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 10] = b4GapPatternWeight 0 2 10 * 0 :=
      b4GapContribution_from_row 0 0 2 10 0 row_00_00_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_10

theorem row_00_00_02_11 : b4RowContribution (![0, 0, 2, 13] : Fin 4 → ℕ) = 3 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨13, by decide⟩⟩ = (![0, 0, 2, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_13
#print axioms Paper7MomentGapNumeric.row_00_00_02_11

theorem weighted_00_00_02_11 : b4RawGapContribution ![0, 0, 2, 11] = 36 := by
  calc
    b4RawGapContribution ![0, 0, 2, 11] = b4GapPatternWeight 0 2 11 * 3 :=
      b4GapContribution_from_row 0 0 2 11 3 row_00_00_02_11
    _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_11

theorem row_00_00_02_12 : b4RowContribution (![0, 0, 2, 14] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨14, by decide⟩⟩ = (![0, 0, 2, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_14
#print axioms Paper7MomentGapNumeric.row_00_00_02_12

theorem weighted_00_00_02_12 : b4RawGapContribution ![0, 0, 2, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 12] = b4GapPatternWeight 0 2 12 * 0 :=
      b4GapContribution_from_row 0 0 2 12 0 row_00_00_02_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_12

theorem row_00_00_02_13 : b4RowContribution (![0, 0, 2, 15] : Fin 4 → ℕ) = 5 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 2, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_15
#print axioms Paper7MomentGapNumeric.row_00_00_02_13

theorem weighted_00_00_02_13 : b4RawGapContribution ![0, 0, 2, 13] = 60 := by
  calc
    b4RawGapContribution ![0, 0, 2, 13] = b4GapPatternWeight 0 2 13 * 5 :=
      b4GapContribution_from_row 0 0 2 13 5 row_00_00_02_13
    _ = 60 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_13

theorem row_00_00_02_14 : b4RowContribution (![0, 0, 2, 16] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 2, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_16
#print axioms Paper7MomentGapNumeric.row_00_00_02_14

theorem weighted_00_00_02_14 : b4RawGapContribution ![0, 0, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 14] = b4GapPatternWeight 0 2 14 * 0 :=
      b4GapContribution_from_row 0 0 2 14 0 row_00_00_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_14

theorem row_00_00_02_15 : b4RowContribution (![0, 0, 2, 17] : Fin 4 → ℕ) = 6 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 2, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_17
#print axioms Paper7MomentGapNumeric.row_00_00_02_15

theorem weighted_00_00_02_15 : b4RawGapContribution ![0, 0, 2, 15] = 72 := by
  calc
    b4RawGapContribution ![0, 0, 2, 15] = b4GapPatternWeight 0 2 15 * 6 :=
      b4GapContribution_from_row 0 0 2 15 6 row_00_00_02_15
    _ = 72 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_15

theorem row_00_00_02_16 : b4RowContribution (![0, 0, 2, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 2, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_18
#print axioms Paper7MomentGapNumeric.row_00_00_02_16

theorem weighted_00_00_02_16 : b4RawGapContribution ![0, 0, 2, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 16] = b4GapPatternWeight 0 2 16 * 0 :=
      b4GapContribution_from_row 0 0 2 16 0 row_00_00_02_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_16

theorem row_00_00_02_17 : b4RowContribution (![0, 0, 2, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 2, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_19
#print axioms Paper7MomentGapNumeric.row_00_00_02_17

theorem weighted_00_00_02_17 : b4RawGapContribution ![0, 0, 2, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 17] = b4GapPatternWeight 0 2 17 * 0 :=
      b4GapContribution_from_row 0 0 2 17 0 row_00_00_02_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_17

theorem row_00_00_02_18 : b4RowContribution (![0, 0, 2, 20] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 2, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_20
#print axioms Paper7MomentGapNumeric.row_00_00_02_18

theorem weighted_00_00_02_18 : b4RawGapContribution ![0, 0, 2, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 18] = b4GapPatternWeight 0 2 18 * 0 :=
      b4GapContribution_from_row 0 0 2 18 0 row_00_00_02_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_18

theorem row_00_00_02_19 : b4RowContribution (![0, 0, 2, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 2, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_21
#print axioms Paper7MomentGapNumeric.row_00_00_02_19

theorem weighted_00_00_02_19 : b4RawGapContribution ![0, 0, 2, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 19] = b4GapPatternWeight 0 2 19 * 0 :=
      b4GapContribution_from_row 0 0 2 19 0 row_00_00_02_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_19

theorem row_00_00_02_20 : b4RowContribution (![0, 0, 2, 22] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 2, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_22
#print axioms Paper7MomentGapNumeric.row_00_00_02_20

theorem weighted_00_00_02_20 : b4RawGapContribution ![0, 0, 2, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 20] = b4GapPatternWeight 0 2 20 * 0 :=
      b4GapContribution_from_row 0 0 2 20 0 row_00_00_02_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_20

theorem row_00_00_02_21 : b4RowContribution (![0, 0, 2, 23] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨23, by decide⟩⟩ = (![0, 0, 2, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_23
#print axioms Paper7MomentGapNumeric.row_00_00_02_21

theorem weighted_00_00_02_21 : b4RawGapContribution ![0, 0, 2, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 21] = b4GapPatternWeight 0 2 21 * 0 :=
      b4GapContribution_from_row 0 0 2 21 0 row_00_00_02_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_21

theorem row_00_00_02_22 : b4RowContribution (![0, 0, 2, 24] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨24, by decide⟩⟩ = (![0, 0, 2, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_24
#print axioms Paper7MomentGapNumeric.row_00_00_02_22

theorem weighted_00_00_02_22 : b4RawGapContribution ![0, 0, 2, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 22] = b4GapPatternWeight 0 2 22 * 0 :=
      b4GapContribution_from_row 0 0 2 22 0 row_00_00_02_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_22

theorem row_00_00_02_23 : b4RowContribution (![0, 0, 2, 25] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨25, by decide⟩⟩ = (![0, 0, 2, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_25
#print axioms Paper7MomentGapNumeric.row_00_00_02_23

theorem weighted_00_00_02_23 : b4RawGapContribution ![0, 0, 2, 23] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 23] = b4GapPatternWeight 0 2 23 * 0 :=
      b4GapContribution_from_row 0 0 2 23 0 row_00_00_02_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_23

theorem row_00_00_02_24 : b4RowContribution (![0, 0, 2, 26] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨26, by decide⟩⟩ = (![0, 0, 2, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_26
#print axioms Paper7MomentGapNumeric.row_00_00_02_24

theorem weighted_00_00_02_24 : b4RawGapContribution ![0, 0, 2, 24] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 24] = b4GapPatternWeight 0 2 24 * 0 :=
      b4GapContribution_from_row 0 0 2 24 0 row_00_00_02_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_24

theorem row_00_00_02_25 : b4RowContribution (![0, 0, 2, 27] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨27, by decide⟩⟩ = (![0, 0, 2, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_27
#print axioms Paper7MomentGapNumeric.row_00_00_02_25

theorem weighted_00_00_02_25 : b4RawGapContribution ![0, 0, 2, 25] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 25] = b4GapPatternWeight 0 2 25 * 0 :=
      b4GapContribution_from_row 0 0 2 25 0 row_00_00_02_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_25

theorem row_00_00_02_26 : b4RowContribution (![0, 0, 2, 28] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨28, by decide⟩⟩ = (![0, 0, 2, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_28
#print axioms Paper7MomentGapNumeric.row_00_00_02_26

theorem weighted_00_00_02_26 : b4RawGapContribution ![0, 0, 2, 26] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 26] = b4GapPatternWeight 0 2 26 * 0 :=
      b4GapContribution_from_row 0 0 2 26 0 row_00_00_02_26
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_26

theorem row_00_00_02_27 : b4RowContribution (![0, 0, 2, 29] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨29, by decide⟩⟩ = (![0, 0, 2, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_29
#print axioms Paper7MomentGapNumeric.row_00_00_02_27

theorem weighted_00_00_02_27 : b4RawGapContribution ![0, 0, 2, 27] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 27] = b4GapPatternWeight 0 2 27 * 0 :=
      b4GapContribution_from_row 0 0 2 27 0 row_00_00_02_27
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_27

theorem row_00_00_02_28 : b4RowContribution (![0, 0, 2, 30] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨30, by decide⟩⟩ = (![0, 0, 2, 30] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_30
#print axioms Paper7MomentGapNumeric.row_00_00_02_28

theorem weighted_00_00_02_28 : b4RawGapContribution ![0, 0, 2, 28] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 28] = b4GapPatternWeight 0 2 28 * 0 :=
      b4GapContribution_from_row 0 0 2 28 0 row_00_00_02_28
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_28

theorem row_00_00_02_29 : b4RowContribution (![0, 0, 2, 31] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨31, by decide⟩⟩ = (![0, 0, 2, 31] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_31
#print axioms Paper7MomentGapNumeric.row_00_00_02_29

theorem weighted_00_00_02_29 : b4RawGapContribution ![0, 0, 2, 29] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 29] = b4GapPatternWeight 0 2 29 * 0 :=
      b4GapContribution_from_row 0 0 2 29 0 row_00_00_02_29
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_29

theorem row_00_00_02_30 : b4RowContribution (![0, 0, 2, 32] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨32, by decide⟩⟩ = (![0, 0, 2, 32] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_32
#print axioms Paper7MomentGapNumeric.row_00_00_02_30

theorem weighted_00_00_02_30 : b4RawGapContribution ![0, 0, 2, 30] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 30] = b4GapPatternWeight 0 2 30 * 0 :=
      b4GapContribution_from_row 0 0 2 30 0 row_00_00_02_30
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_30

theorem row_00_00_02_31 : b4RowContribution (![0, 0, 2, 33] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨33, by decide⟩⟩ = (![0, 0, 2, 33] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_33
#print axioms Paper7MomentGapNumeric.row_00_00_02_31

theorem weighted_00_00_02_31 : b4RawGapContribution ![0, 0, 2, 31] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 31] = b4GapPatternWeight 0 2 31 * 0 :=
      b4GapContribution_from_row 0 0 2 31 0 row_00_00_02_31
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_31

theorem row_00_00_02_32 : b4RowContribution (![0, 0, 2, 34] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨34, by decide⟩⟩ = (![0, 0, 2, 34] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_34
#print axioms Paper7MomentGapNumeric.row_00_00_02_32

theorem weighted_00_00_02_32 : b4RawGapContribution ![0, 0, 2, 32] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 32] = b4GapPatternWeight 0 2 32 * 0 :=
      b4GapContribution_from_row 0 0 2 32 0 row_00_00_02_32
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_32

theorem row_00_00_02_33 : b4RowContribution (![0, 0, 2, 35] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨2, by decide⟩, ⟨35, by decide⟩⟩ = (![0, 0, 2, 35] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_02_35
#print axioms Paper7MomentGapNumeric.row_00_00_02_33

theorem weighted_00_00_02_33 : b4RawGapContribution ![0, 0, 2, 33] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 2, 33] = b4GapPatternWeight 0 2 33 * 0 :=
      b4GapContribution_from_row 0 0 2 33 0 row_00_00_02_33
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_02_33

def dvalues_00_00_02 : Fin 34 → ℕ := ![0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 36, 0, 60, 0, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_02

theorem dblock_00_00_02 : b4GapPatternDBlock 0 0 2 = 204 := by
  calc
    b4GapPatternDBlock 0 0 2 = ∑ d : Fin 34, dvalues_00_00_02 d := by
      apply b4GapDBlock_of_rows 0 0 2 dvalues_00_00_02
      intro d
      fin_cases d
      · exact weighted_00_00_02_00
      · exact weighted_00_00_02_01
      · exact weighted_00_00_02_02
      · exact weighted_00_00_02_03
      · exact weighted_00_00_02_04
      · exact weighted_00_00_02_05
      · exact weighted_00_00_02_06
      · exact weighted_00_00_02_07
      · exact weighted_00_00_02_08
      · exact weighted_00_00_02_09
      · exact weighted_00_00_02_10
      · exact weighted_00_00_02_11
      · exact weighted_00_00_02_12
      · exact weighted_00_00_02_13
      · exact weighted_00_00_02_14
      · exact weighted_00_00_02_15
      · exact weighted_00_00_02_16
      · exact weighted_00_00_02_17
      · exact weighted_00_00_02_18
      · exact weighted_00_00_02_19
      · exact weighted_00_00_02_20
      · exact weighted_00_00_02_21
      · exact weighted_00_00_02_22
      · exact weighted_00_00_02_23
      · exact weighted_00_00_02_24
      · exact weighted_00_00_02_25
      · exact weighted_00_00_02_26
      · exact weighted_00_00_02_27
      · exact weighted_00_00_02_28
      · exact weighted_00_00_02_29
      · exact weighted_00_00_02_30
      · exact weighted_00_00_02_31
      · exact weighted_00_00_02_32
      · exact weighted_00_00_02_33
    _ = 204 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_02

end Paper7MomentGapNumeric
