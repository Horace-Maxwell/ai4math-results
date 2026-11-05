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

theorem row_04_02_04_00 : b4RowContribution (![4, 6, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 10, 10] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 10 + 10 = 30
    decide
  have hzsq : (∑ i, (((![4, 6, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 252 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 10^2 + 10^2 = 252
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_04_00

theorem weighted_04_02_04_00 : b4RawGapContribution ![4, 2, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 4, 0] = b4GapPatternWeight 2 4 0 * 0 :=
      b4GapContribution_from_row 4 2 4 0 0 row_04_02_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_04_00

theorem row_04_02_04_01 : b4RowContribution (![4, 6, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 10, 11] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 10 + 11 = 31
    decide
  have hzsq : (∑ i, (((![4, 6, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 273 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 10^2 + 11^2 = 273
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_04_01

theorem weighted_04_02_04_01 : b4RawGapContribution ![4, 2, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 4, 1] = b4GapPatternWeight 2 4 1 * 0 :=
      b4GapContribution_from_row 4 2 4 1 0 row_04_02_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_04_01

theorem row_04_02_04_02 : b4RowContribution (![4, 6, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 10, 12] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 10 + 12 = 32
    decide
  have hzsq : (∑ i, (((![4, 6, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 296 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 10^2 + 12^2 = 296
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_04_02

theorem weighted_04_02_04_02 : b4RawGapContribution ![4, 2, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 4, 2] = b4GapPatternWeight 2 4 2 * 0 :=
      b4GapContribution_from_row 4 2 4 2 0 row_04_02_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_04_02

theorem row_04_02_04_03 : b4RowContribution (![4, 6, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 10, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 10 + 13 = 33
    decide
  have hzsq : (∑ i, (((![4, 6, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 321 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 10^2 + 13^2 = 321
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_04_03

theorem weighted_04_02_04_03 : b4RawGapContribution ![4, 2, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 4, 3] = b4GapPatternWeight 2 4 3 * 0 :=
      b4GapContribution_from_row 4 2 4 3 0 row_04_02_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_04_03

theorem row_04_02_04_04 : b4RowContribution (![4, 6, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 10, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 10 + 14 = 34
    decide
  have hzsq : (∑ i, (((![4, 6, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 348 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 10^2 + 14^2 = 348
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_04_04

theorem weighted_04_02_04_04 : b4RawGapContribution ![4, 2, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 4, 4] = b4GapPatternWeight 2 4 4 * 0 :=
      b4GapContribution_from_row 4 2 4 4 0 row_04_02_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_04_04

theorem row_04_02_04_05 : b4RowContribution (![4, 6, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 10, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 10 + 15 = 35
    decide
  have hzsq : (∑ i, (((![4, 6, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 377 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 10^2 + 15^2 = 377
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_04_05

theorem weighted_04_02_04_05 : b4RawGapContribution ![4, 2, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 4, 5] = b4GapPatternWeight 2 4 5 * 0 :=
      b4GapContribution_from_row 4 2 4 5 0 row_04_02_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_04_05

theorem row_04_02_04_06 : b4RowContribution (![4, 6, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 10, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 10 + 16 = 36
    decide
  have hzsq : (∑ i, (((![4, 6, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 408 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 10^2 + 16^2 = 408
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_04_06

theorem weighted_04_02_04_06 : b4RawGapContribution ![4, 2, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 4, 6] = b4GapPatternWeight 2 4 6 * 0 :=
      b4GapContribution_from_row 4 2 4 6 0 row_04_02_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_04_06

theorem row_04_02_04_07 : b4RowContribution (![4, 6, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 10, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 10 + 17 = 37
    decide
  have hzsq : (∑ i, (((![4, 6, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 441 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 10^2 + 17^2 = 441
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_04_07

theorem weighted_04_02_04_07 : b4RawGapContribution ![4, 2, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 4, 7] = b4GapPatternWeight 2 4 7 * 0 :=
      b4GapContribution_from_row 4 2 4 7 0 row_04_02_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_04_07

def dvalues_04_02_04 : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_02_04

theorem dblock_04_02_04 : b4GapPatternDBlock 4 2 4 = 0 := by
  calc
    b4GapPatternDBlock 4 2 4 = ∑ d : Fin 8, dvalues_04_02_04 d := by
      apply b4GapDBlock_of_rows 4 2 4 dvalues_04_02_04
      intro d
      fin_cases d
      · exact weighted_04_02_04_00
      · exact weighted_04_02_04_01
      · exact weighted_04_02_04_02
      · exact weighted_04_02_04_03
      · exact weighted_04_02_04_04
      · exact weighted_04_02_04_05
      · exact weighted_04_02_04_06
      · exact weighted_04_02_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_02_04

end Paper7MomentGapNumeric
