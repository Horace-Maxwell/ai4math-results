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

theorem row_01_05_07_00 : b4RowContribution (![1, 6, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 13, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 13 + 13 = 33
    decide
  have hzsq : (∑ i, (((![1, 6, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 375 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 13^2 + 13^2 = 375
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_07_00

theorem weighted_01_05_07_00 : b4RawGapContribution ![1, 5, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 7, 0] = b4GapPatternWeight 5 7 0 * 0 :=
      b4GapContribution_from_row 1 5 7 0 0 row_01_05_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_07_00

theorem row_01_05_07_01 : b4RowContribution (![1, 6, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 13, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 13 + 14 = 34
    decide
  have hzsq : (∑ i, (((![1, 6, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 402 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 13^2 + 14^2 = 402
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_07_01

theorem weighted_01_05_07_01 : b4RawGapContribution ![1, 5, 7, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 7, 1] = b4GapPatternWeight 5 7 1 * 0 :=
      b4GapContribution_from_row 1 5 7 1 0 row_01_05_07_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_07_01

theorem row_01_05_07_02 : b4RowContribution (![1, 6, 13, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 13, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 13 + 15 = 35
    decide
  have hzsq : (∑ i, (((![1, 6, 13, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 431 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 13^2 + 15^2 = 431
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_07_02

theorem weighted_01_05_07_02 : b4RawGapContribution ![1, 5, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 7, 2] = b4GapPatternWeight 5 7 2 * 0 :=
      b4GapContribution_from_row 1 5 7 2 0 row_01_05_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_07_02

theorem row_01_05_07_03 : b4RowContribution (![1, 6, 13, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 13, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 13 + 16 = 36
    decide
  have hzsq : (∑ i, (((![1, 6, 13, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 462 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 13^2 + 16^2 = 462
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_07_03

theorem weighted_01_05_07_03 : b4RawGapContribution ![1, 5, 7, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 7, 3] = b4GapPatternWeight 5 7 3 * 0 :=
      b4GapContribution_from_row 1 5 7 3 0 row_01_05_07_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_07_03

theorem row_01_05_07_04 : b4RowContribution (![1, 6, 13, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 13, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 13 + 17 = 37
    decide
  have hzsq : (∑ i, (((![1, 6, 13, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 495 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 13^2 + 17^2 = 495
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_07_04

theorem weighted_01_05_07_04 : b4RawGapContribution ![1, 5, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 7, 4] = b4GapPatternWeight 5 7 4 * 0 :=
      b4GapContribution_from_row 1 5 7 4 0 row_01_05_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_07_04

def dvalues_01_05_07 : Fin 5 → ℕ := ![0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_05_07

theorem dblock_01_05_07 : b4GapPatternDBlock 1 5 7 = 0 := by
  calc
    b4GapPatternDBlock 1 5 7 = ∑ d : Fin 5, dvalues_01_05_07 d := by
      apply b4GapDBlock_of_rows 1 5 7 dvalues_01_05_07
      intro d
      fin_cases d
      · exact weighted_01_05_07_00
      · exact weighted_01_05_07_01
      · exact weighted_01_05_07_02
      · exact weighted_01_05_07_03
      · exact weighted_01_05_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_05_07

end Paper7MomentGapNumeric
