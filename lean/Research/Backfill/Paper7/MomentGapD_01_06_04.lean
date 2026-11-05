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

theorem row_01_06_04_00 : b4RowContribution (![1, 7, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 11, 11] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 11 + 11 = 30
    decide
  have hzsq : (∑ i, (((![1, 7, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 292 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 11^2 + 11^2 = 292
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_04_00

theorem weighted_01_06_04_00 : b4RawGapContribution ![1, 6, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 4, 0] = b4GapPatternWeight 6 4 0 * 0 :=
      b4GapContribution_from_row 1 6 4 0 0 row_01_06_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_04_00

theorem row_01_06_04_01 : b4RowContribution (![1, 7, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 11, 12] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 11 + 12 = 31
    decide
  have hzsq : (∑ i, (((![1, 7, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 315 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 11^2 + 12^2 = 315
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_04_01

theorem weighted_01_06_04_01 : b4RawGapContribution ![1, 6, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 4, 1] = b4GapPatternWeight 6 4 1 * 0 :=
      b4GapContribution_from_row 1 6 4 1 0 row_01_06_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_04_01

theorem row_01_06_04_02 : b4RowContribution (![1, 7, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 11, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 11 + 13 = 32
    decide
  have hzsq : (∑ i, (((![1, 7, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 340 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 11^2 + 13^2 = 340
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_04_02

theorem weighted_01_06_04_02 : b4RawGapContribution ![1, 6, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 4, 2] = b4GapPatternWeight 6 4 2 * 0 :=
      b4GapContribution_from_row 1 6 4 2 0 row_01_06_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_04_02

theorem row_01_06_04_03 : b4RowContribution (![1, 7, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 11, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 11 + 14 = 33
    decide
  have hzsq : (∑ i, (((![1, 7, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 367 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 11^2 + 14^2 = 367
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_04_03

theorem weighted_01_06_04_03 : b4RawGapContribution ![1, 6, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 4, 3] = b4GapPatternWeight 6 4 3 * 0 :=
      b4GapContribution_from_row 1 6 4 3 0 row_01_06_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_04_03

theorem row_01_06_04_04 : b4RowContribution (![1, 7, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 11, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 11 + 15 = 34
    decide
  have hzsq : (∑ i, (((![1, 7, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 396 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 11^2 + 15^2 = 396
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_04_04

theorem weighted_01_06_04_04 : b4RawGapContribution ![1, 6, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 4, 4] = b4GapPatternWeight 6 4 4 * 0 :=
      b4GapContribution_from_row 1 6 4 4 0 row_01_06_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_04_04

theorem row_01_06_04_05 : b4RowContribution (![1, 7, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 11, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 11 + 16 = 35
    decide
  have hzsq : (∑ i, (((![1, 7, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 427 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 11^2 + 16^2 = 427
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_04_05

theorem weighted_01_06_04_05 : b4RawGapContribution ![1, 6, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 4, 5] = b4GapPatternWeight 6 4 5 * 0 :=
      b4GapContribution_from_row 1 6 4 5 0 row_01_06_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_04_05

theorem row_01_06_04_06 : b4RowContribution (![1, 7, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 11, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 11 + 17 = 36
    decide
  have hzsq : (∑ i, (((![1, 7, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 460 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 11^2 + 17^2 = 460
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_04_06

theorem weighted_01_06_04_06 : b4RawGapContribution ![1, 6, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 4, 6] = b4GapPatternWeight 6 4 6 * 0 :=
      b4GapContribution_from_row 1 6 4 6 0 row_01_06_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_04_06

theorem row_01_06_04_07 : b4RowContribution (![1, 7, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 11, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 11 + 18 = 37
    decide
  have hzsq : (∑ i, (((![1, 7, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 495 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 11^2 + 18^2 = 495
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_04_07

theorem weighted_01_06_04_07 : b4RawGapContribution ![1, 6, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 4, 7] = b4GapPatternWeight 6 4 7 * 0 :=
      b4GapContribution_from_row 1 6 4 7 0 row_01_06_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_04_07

def dvalues_01_06_04 : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_06_04

theorem dblock_01_06_04 : b4GapPatternDBlock 1 6 4 = 0 := by
  calc
    b4GapPatternDBlock 1 6 4 = ∑ d : Fin 8, dvalues_01_06_04 d := by
      apply b4GapDBlock_of_rows 1 6 4 dvalues_01_06_04
      intro d
      fin_cases d
      · exact weighted_01_06_04_00
      · exact weighted_01_06_04_01
      · exact weighted_01_06_04_02
      · exact weighted_01_06_04_03
      · exact weighted_01_06_04_04
      · exact weighted_01_06_04_05
      · exact weighted_01_06_04_06
      · exact weighted_01_06_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_06_04

end Paper7MomentGapNumeric
