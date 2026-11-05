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

theorem row_02_05_04_00 : b4RowContribution (![2, 7, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 11, 11] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 11 + 11 = 31
    decide
  have hzsq : (∑ i, (((![2, 7, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 295 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 11^2 + 11^2 = 295
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_04_00

theorem weighted_02_05_04_00 : b4RawGapContribution ![2, 5, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 4, 0] = b4GapPatternWeight 5 4 0 * 0 :=
      b4GapContribution_from_row 2 5 4 0 0 row_02_05_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_04_00

theorem row_02_05_04_01 : b4RowContribution (![2, 7, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 11, 12] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 11 + 12 = 32
    decide
  have hzsq : (∑ i, (((![2, 7, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 318 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 11^2 + 12^2 = 318
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_04_01

theorem weighted_02_05_04_01 : b4RawGapContribution ![2, 5, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 4, 1] = b4GapPatternWeight 5 4 1 * 0 :=
      b4GapContribution_from_row 2 5 4 1 0 row_02_05_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_04_01

theorem row_02_05_04_02 : b4RowContribution (![2, 7, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 11, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 11 + 13 = 33
    decide
  have hzsq : (∑ i, (((![2, 7, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 343 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 11^2 + 13^2 = 343
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_04_02

theorem weighted_02_05_04_02 : b4RawGapContribution ![2, 5, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 4, 2] = b4GapPatternWeight 5 4 2 * 0 :=
      b4GapContribution_from_row 2 5 4 2 0 row_02_05_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_04_02

theorem row_02_05_04_03 : b4RowContribution (![2, 7, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 11, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 11 + 14 = 34
    decide
  have hzsq : (∑ i, (((![2, 7, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 370 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 11^2 + 14^2 = 370
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_04_03

theorem weighted_02_05_04_03 : b4RawGapContribution ![2, 5, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 4, 3] = b4GapPatternWeight 5 4 3 * 0 :=
      b4GapContribution_from_row 2 5 4 3 0 row_02_05_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_04_03

theorem row_02_05_04_04 : b4RowContribution (![2, 7, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 11, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 11 + 15 = 35
    decide
  have hzsq : (∑ i, (((![2, 7, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 399 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 11^2 + 15^2 = 399
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_04_04

theorem weighted_02_05_04_04 : b4RawGapContribution ![2, 5, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 4, 4] = b4GapPatternWeight 5 4 4 * 0 :=
      b4GapContribution_from_row 2 5 4 4 0 row_02_05_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_04_04

theorem row_02_05_04_05 : b4RowContribution (![2, 7, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 11, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 11 + 16 = 36
    decide
  have hzsq : (∑ i, (((![2, 7, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 430 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 11^2 + 16^2 = 430
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_04_05

theorem weighted_02_05_04_05 : b4RawGapContribution ![2, 5, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 4, 5] = b4GapPatternWeight 5 4 5 * 0 :=
      b4GapContribution_from_row 2 5 4 5 0 row_02_05_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_04_05

theorem row_02_05_04_06 : b4RowContribution (![2, 7, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 11, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 11 + 17 = 37
    decide
  have hzsq : (∑ i, (((![2, 7, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 463 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 11^2 + 17^2 = 463
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_04_06

theorem weighted_02_05_04_06 : b4RawGapContribution ![2, 5, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 4, 6] = b4GapPatternWeight 5 4 6 * 0 :=
      b4GapContribution_from_row 2 5 4 6 0 row_02_05_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_04_06

def dvalues_02_05_04 : Fin 7 → ℕ := ![0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_05_04

theorem dblock_02_05_04 : b4GapPatternDBlock 2 5 4 = 0 := by
  calc
    b4GapPatternDBlock 2 5 4 = ∑ d : Fin 7, dvalues_02_05_04 d := by
      apply b4GapDBlock_of_rows 2 5 4 dvalues_02_05_04
      intro d
      fin_cases d
      · exact weighted_02_05_04_00
      · exact weighted_02_05_04_01
      · exact weighted_02_05_04_02
      · exact weighted_02_05_04_03
      · exact weighted_02_05_04_04
      · exact weighted_02_05_04_05
      · exact weighted_02_05_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_05_04

end Paper7MomentGapNumeric
