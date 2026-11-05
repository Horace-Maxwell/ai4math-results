import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4Block00C13

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

theorem row_00_00_13_00 : b4RowContribution (![0, 0, 13, 13] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨13, by decide⟩, ⟨13, by decide⟩⟩ = (![0, 0, 13, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_13_13
#print axioms Paper7MomentGapNumeric.row_00_00_13_00

theorem weighted_00_00_13_00 : b4RawGapContribution ![0, 0, 13, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 13, 0] = b4GapPatternWeight 0 13 0 * 0 :=
      b4GapContribution_from_row 0 0 13 0 0 row_00_00_13_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_13_00

theorem row_00_00_13_01 : b4RowContribution (![0, 0, 13, 14] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨13, by decide⟩, ⟨14, by decide⟩⟩ = (![0, 0, 13, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_13_14
#print axioms Paper7MomentGapNumeric.row_00_00_13_01

theorem weighted_00_00_13_01 : b4RawGapContribution ![0, 0, 13, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 13, 1] = b4GapPatternWeight 0 13 1 * 0 :=
      b4GapContribution_from_row 0 0 13 1 0 row_00_00_13_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_13_01

theorem row_00_00_13_02 : b4RowContribution (![0, 0, 13, 15] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨13, by decide⟩, ⟨15, by decide⟩⟩ = (![0, 0, 13, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_13_15
#print axioms Paper7MomentGapNumeric.row_00_00_13_02

theorem weighted_00_00_13_02 : b4RawGapContribution ![0, 0, 13, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 13, 2] = b4GapPatternWeight 0 13 2 * 0 :=
      b4GapContribution_from_row 0 0 13 2 0 row_00_00_13_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_13_02

theorem row_00_00_13_03 : b4RowContribution (![0, 0, 13, 16] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨13, by decide⟩, ⟨16, by decide⟩⟩ = (![0, 0, 13, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_13_16
#print axioms Paper7MomentGapNumeric.row_00_00_13_03

theorem weighted_00_00_13_03 : b4RawGapContribution ![0, 0, 13, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 13, 3] = b4GapPatternWeight 0 13 3 * 0 :=
      b4GapContribution_from_row 0 0 13 3 0 row_00_00_13_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_13_03

theorem row_00_00_13_04 : b4RowContribution (![0, 0, 13, 17] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨13, by decide⟩, ⟨17, by decide⟩⟩ = (![0, 0, 13, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_13_17
#print axioms Paper7MomentGapNumeric.row_00_00_13_04

theorem weighted_00_00_13_04 : b4RawGapContribution ![0, 0, 13, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 13, 4] = b4GapPatternWeight 0 13 4 * 0 :=
      b4GapContribution_from_row 0 0 13 4 0 row_00_00_13_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_13_04

theorem row_00_00_13_05 : b4RowContribution (![0, 0, 13, 18] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨13, by decide⟩, ⟨18, by decide⟩⟩ = (![0, 0, 13, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_13_18
#print axioms Paper7MomentGapNumeric.row_00_00_13_05

theorem weighted_00_00_13_05 : b4RawGapContribution ![0, 0, 13, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 13, 5] = b4GapPatternWeight 0 13 5 * 0 :=
      b4GapContribution_from_row 0 0 13 5 0 row_00_00_13_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_13_05

theorem row_00_00_13_06 : b4RowContribution (![0, 0, 13, 19] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨13, by decide⟩, ⟨19, by decide⟩⟩ = (![0, 0, 13, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_13_19
#print axioms Paper7MomentGapNumeric.row_00_00_13_06

theorem weighted_00_00_13_06 : b4RawGapContribution ![0, 0, 13, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 13, 6] = b4GapPatternWeight 0 13 6 * 0 :=
      b4GapContribution_from_row 0 0 13 6 0 row_00_00_13_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_13_06

theorem row_00_00_13_07 : b4RowContribution (![0, 0, 13, 20] : Fin 4 → ℕ) = 3 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨13, by decide⟩, ⟨20, by decide⟩⟩ = (![0, 0, 13, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_13_20
#print axioms Paper7MomentGapNumeric.row_00_00_13_07

theorem weighted_00_00_13_07 : b4RawGapContribution ![0, 0, 13, 7] = 36 := by
  calc
    b4RawGapContribution ![0, 0, 13, 7] = b4GapPatternWeight 0 13 7 * 3 :=
      b4GapContribution_from_row 0 0 13 7 3 row_00_00_13_07
    _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_13_07

theorem row_00_00_13_08 : b4RowContribution (![0, 0, 13, 21] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨13, by decide⟩, ⟨21, by decide⟩⟩ = (![0, 0, 13, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_13_21
#print axioms Paper7MomentGapNumeric.row_00_00_13_08

theorem weighted_00_00_13_08 : b4RawGapContribution ![0, 0, 13, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 13, 8] = b4GapPatternWeight 0 13 8 * 0 :=
      b4GapContribution_from_row 0 0 13 8 0 row_00_00_13_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_13_08

theorem row_00_00_13_09 : b4RowContribution (![0, 0, 13, 22] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨13, by decide⟩, ⟨22, by decide⟩⟩ = (![0, 0, 13, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_13_22
#print axioms Paper7MomentGapNumeric.row_00_00_13_09

theorem weighted_00_00_13_09 : b4RawGapContribution ![0, 0, 13, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 13, 9] = b4GapPatternWeight 0 13 9 * 0 :=
      b4GapContribution_from_row 0 0 13 9 0 row_00_00_13_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_13_09

theorem row_00_00_13_10 : b4RowContribution (![0, 0, 13, 23] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨13, by decide⟩, ⟨23, by decide⟩⟩ = (![0, 0, 13, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_13_23
#print axioms Paper7MomentGapNumeric.row_00_00_13_10

theorem weighted_00_00_13_10 : b4RawGapContribution ![0, 0, 13, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 13, 10] = b4GapPatternWeight 0 13 10 * 0 :=
      b4GapContribution_from_row 0 0 13 10 0 row_00_00_13_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_13_10

theorem row_00_00_13_11 : b4RowContribution (![0, 0, 13, 24] : Fin 4 → ℕ) = 0 := by
  have hz : b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩,
      ⟨13, by decide⟩, ⟨24, by decide⟩⟩ = (![0, 0, 13, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hz] using Paper7MomentBlock00.row_13_24
#print axioms Paper7MomentGapNumeric.row_00_00_13_11

theorem weighted_00_00_13_11 : b4RawGapContribution ![0, 0, 13, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 0, 13, 11] = b4GapPatternWeight 0 13 11 * 0 :=
      b4GapContribution_from_row 0 0 13 11 0 row_00_00_13_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_00_13_11

def dvalues_00_00_13 : Fin 12 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_00_13

theorem dblock_00_00_13 : b4GapPatternDBlock 0 0 13 = 36 := by
  calc
    b4GapPatternDBlock 0 0 13 = ∑ d : Fin 12, dvalues_00_00_13 d := by
      apply b4GapDBlock_of_rows 0 0 13 dvalues_00_00_13
      intro d
      fin_cases d
      · exact weighted_00_00_13_00
      · exact weighted_00_00_13_01
      · exact weighted_00_00_13_02
      · exact weighted_00_00_13_03
      · exact weighted_00_00_13_04
      · exact weighted_00_00_13_05
      · exact weighted_00_00_13_06
      · exact weighted_00_00_13_07
      · exact weighted_00_00_13_08
      · exact weighted_00_00_13_09
      · exact weighted_00_00_13_10
      · exact weighted_00_00_13_11
    _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_00_13

end Paper7MomentGapNumeric
