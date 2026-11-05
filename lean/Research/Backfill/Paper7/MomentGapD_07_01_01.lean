import Research.Backfill.Paper7.B4GapBlockAssembly
import Research.Backfill.Paper7.SparseRowCertificate

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

theorem row_07_01_01_00 : b4RowContribution (![7, 8, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 8, 9, 9] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 7 + 8 + 9 + 9 = 33
    decide
  have hzsq : (∑ i, (((![7, 8, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 275 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 8^2 + 9^2 + 9^2 = 275
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_01_01_00

theorem weighted_07_01_01_00 : b4RawGapContribution ![7, 1, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![7, 1, 1, 0] = b4GapPatternWeight 1 1 0 * 0 :=
      b4GapContribution_from_row 7 1 1 0 0 row_07_01_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_01_01_00

theorem row_07_01_01_01 : b4RowContribution (![7, 8, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 8, 9, 10] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 7 + 8 + 9 + 10 = 34
    decide
  have hzsq : (∑ i, (((![7, 8, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 294 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 8^2 + 9^2 + 10^2 = 294
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_01_01_01

theorem weighted_07_01_01_01 : b4RawGapContribution ![7, 1, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![7, 1, 1, 1] = b4GapPatternWeight 1 1 1 * 0 :=
      b4GapContribution_from_row 7 1 1 1 0 row_07_01_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_01_01_01

theorem row_07_01_01_02 : b4RowContribution (![7, 8, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 8, 9, 11] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 7 + 8 + 9 + 11 = 35
    decide
  have hzsq : (∑ i, (((![7, 8, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 315 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 8^2 + 9^2 + 11^2 = 315
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_01_01_02

theorem weighted_07_01_01_02 : b4RawGapContribution ![7, 1, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![7, 1, 1, 2] = b4GapPatternWeight 1 1 2 * 0 :=
      b4GapContribution_from_row 7 1 1 2 0 row_07_01_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_01_01_02

theorem row_07_01_01_03 : b4RowContribution (![7, 8, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 8, 9, 12] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 7 + 8 + 9 + 12 = 36
    decide
  have hzsq : (∑ i, (((![7, 8, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 338 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 8^2 + 9^2 + 12^2 = 338
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_01_01_03

theorem weighted_07_01_01_03 : b4RawGapContribution ![7, 1, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![7, 1, 1, 3] = b4GapPatternWeight 1 1 3 * 0 :=
      b4GapContribution_from_row 7 1 1 3 0 row_07_01_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_01_01_03

theorem row_07_01_01_04 : b4RowContribution (![7, 8, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 8, 9, 13] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 7 + 8 + 9 + 13 = 37
    decide
  have hzsq : (∑ i, (((![7, 8, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 363 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 8^2 + 9^2 + 13^2 = 363
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_01_01_04

theorem weighted_07_01_01_04 : b4RawGapContribution ![7, 1, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![7, 1, 1, 4] = b4GapPatternWeight 1 1 4 * 0 :=
      b4GapContribution_from_row 7 1 1 4 0 row_07_01_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_01_01_04

def dvalues_07_01_01 : Fin 5 → ℕ := ![0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_07_01_01

theorem dblock_07_01_01 : b4GapPatternDBlock 7 1 1 = 0 := by
  calc
    b4GapPatternDBlock 7 1 1 = ∑ d : Fin 5, dvalues_07_01_01 d := by
      apply b4GapDBlock_of_rows 7 1 1 dvalues_07_01_01
      intro d
      fin_cases d
      · exact weighted_07_01_01_00
      · exact weighted_07_01_01_01
      · exact weighted_07_01_01_02
      · exact weighted_07_01_01_03
      · exact weighted_07_01_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_07_01_01

end Paper7MomentGapNumeric
