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

theorem row_03_03_05_00 : b4RowContribution (![3, 6, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 11, 11] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 11 + 11 = 31
    decide
  have hzsq : (∑ i, (((![3, 6, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 287 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 11^2 + 11^2 = 287
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_05_00

theorem weighted_03_03_05_00 : b4RawGapContribution ![3, 3, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 5, 0] = b4GapPatternWeight 3 5 0 * 0 :=
      b4GapContribution_from_row 3 3 5 0 0 row_03_03_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_05_00

theorem row_03_03_05_01 : b4RowContribution (![3, 6, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 11, 12] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 11 + 12 = 32
    decide
  have hzsq : (∑ i, (((![3, 6, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 310 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 11^2 + 12^2 = 310
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_05_01

theorem weighted_03_03_05_01 : b4RawGapContribution ![3, 3, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 5, 1] = b4GapPatternWeight 3 5 1 * 0 :=
      b4GapContribution_from_row 3 3 5 1 0 row_03_03_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_05_01

theorem row_03_03_05_02 : b4RowContribution (![3, 6, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 11, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 11 + 13 = 33
    decide
  have hzsq : (∑ i, (((![3, 6, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 335 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 11^2 + 13^2 = 335
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_05_02

theorem weighted_03_03_05_02 : b4RawGapContribution ![3, 3, 5, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 5, 2] = b4GapPatternWeight 3 5 2 * 0 :=
      b4GapContribution_from_row 3 3 5 2 0 row_03_03_05_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_05_02

theorem row_03_03_05_03 : b4RowContribution (![3, 6, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 11, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 11 + 14 = 34
    decide
  have hzsq : (∑ i, (((![3, 6, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 362 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 11^2 + 14^2 = 362
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_05_03

theorem weighted_03_03_05_03 : b4RawGapContribution ![3, 3, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 5, 3] = b4GapPatternWeight 3 5 3 * 0 :=
      b4GapContribution_from_row 3 3 5 3 0 row_03_03_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_05_03

theorem row_03_03_05_04 : b4RowContribution (![3, 6, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 11, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 11 + 15 = 35
    decide
  have hzsq : (∑ i, (((![3, 6, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 391 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 11^2 + 15^2 = 391
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_05_04

theorem weighted_03_03_05_04 : b4RawGapContribution ![3, 3, 5, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 5, 4] = b4GapPatternWeight 3 5 4 * 0 :=
      b4GapContribution_from_row 3 3 5 4 0 row_03_03_05_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_05_04

theorem row_03_03_05_05 : b4RowContribution (![3, 6, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 11, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 11 + 16 = 36
    decide
  have hzsq : (∑ i, (((![3, 6, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 422 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 11^2 + 16^2 = 422
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_05_05

theorem weighted_03_03_05_05 : b4RawGapContribution ![3, 3, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 5, 5] = b4GapPatternWeight 3 5 5 * 0 :=
      b4GapContribution_from_row 3 3 5 5 0 row_03_03_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_05_05

theorem row_03_03_05_06 : b4RowContribution (![3, 6, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 11, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 11 + 17 = 37
    decide
  have hzsq : (∑ i, (((![3, 6, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 455 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 11^2 + 17^2 = 455
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_05_06

theorem weighted_03_03_05_06 : b4RawGapContribution ![3, 3, 5, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 5, 6] = b4GapPatternWeight 3 5 6 * 0 :=
      b4GapContribution_from_row 3 3 5 6 0 row_03_03_05_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_05_06

def dvalues_03_03_05 : Fin 7 → ℕ := ![0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_03_05

theorem dblock_03_03_05 : b4GapPatternDBlock 3 3 5 = 0 := by
  calc
    b4GapPatternDBlock 3 3 5 = ∑ d : Fin 7, dvalues_03_03_05 d := by
      apply b4GapDBlock_of_rows 3 3 5 dvalues_03_03_05
      intro d
      fin_cases d
      · exact weighted_03_03_05_00
      · exact weighted_03_03_05_01
      · exact weighted_03_03_05_02
      · exact weighted_03_03_05_03
      · exact weighted_03_03_05_04
      · exact weighted_03_03_05_05
      · exact weighted_03_03_05_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_03_05

end Paper7MomentGapNumeric
