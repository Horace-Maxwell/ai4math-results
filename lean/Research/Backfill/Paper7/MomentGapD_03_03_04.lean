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

theorem row_03_03_04_00 : b4RowContribution (![3, 6, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 10, 10] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 10 + 10 = 29
    decide
  have hzsq : (∑ i, (((![3, 6, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 245 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 10^2 + 10^2 = 245
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_04_00

theorem weighted_03_03_04_00 : b4RawGapContribution ![3, 3, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 4, 0] = b4GapPatternWeight 3 4 0 * 0 :=
      b4GapContribution_from_row 3 3 4 0 0 row_03_03_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_04_00

theorem row_03_03_04_01 : b4RowContribution (![3, 6, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 10, 11] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 10 + 11 = 30
    decide
  have hzsq : (∑ i, (((![3, 6, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 266 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 10^2 + 11^2 = 266
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_04_01

theorem weighted_03_03_04_01 : b4RawGapContribution ![3, 3, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 4, 1] = b4GapPatternWeight 3 4 1 * 0 :=
      b4GapContribution_from_row 3 3 4 1 0 row_03_03_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_04_01

theorem row_03_03_04_02 : b4RowContribution (![3, 6, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 10, 12] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 10 + 12 = 31
    decide
  have hzsq : (∑ i, (((![3, 6, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 289 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 10^2 + 12^2 = 289
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_04_02

theorem weighted_03_03_04_02 : b4RawGapContribution ![3, 3, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 4, 2] = b4GapPatternWeight 3 4 2 * 0 :=
      b4GapContribution_from_row 3 3 4 2 0 row_03_03_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_04_02

theorem row_03_03_04_03 : b4RowContribution (![3, 6, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 10, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 10 + 13 = 32
    decide
  have hzsq : (∑ i, (((![3, 6, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 314 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 10^2 + 13^2 = 314
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_04_03

theorem weighted_03_03_04_03 : b4RawGapContribution ![3, 3, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 4, 3] = b4GapPatternWeight 3 4 3 * 0 :=
      b4GapContribution_from_row 3 3 4 3 0 row_03_03_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_04_03

theorem row_03_03_04_04 : b4RowContribution (![3, 6, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 10, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 10 + 14 = 33
    decide
  have hzsq : (∑ i, (((![3, 6, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 341 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 10^2 + 14^2 = 341
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_04_04

theorem weighted_03_03_04_04 : b4RawGapContribution ![3, 3, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 4, 4] = b4GapPatternWeight 3 4 4 * 0 :=
      b4GapContribution_from_row 3 3 4 4 0 row_03_03_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_04_04

theorem row_03_03_04_05 : b4RowContribution (![3, 6, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 10, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 10 + 15 = 34
    decide
  have hzsq : (∑ i, (((![3, 6, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 370 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 10^2 + 15^2 = 370
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_04_05

theorem weighted_03_03_04_05 : b4RawGapContribution ![3, 3, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 4, 5] = b4GapPatternWeight 3 4 5 * 0 :=
      b4GapContribution_from_row 3 3 4 5 0 row_03_03_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_04_05

theorem row_03_03_04_06 : b4RowContribution (![3, 6, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 10, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 10 + 16 = 35
    decide
  have hzsq : (∑ i, (((![3, 6, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 401 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 10^2 + 16^2 = 401
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_04_06

theorem weighted_03_03_04_06 : b4RawGapContribution ![3, 3, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 4, 6] = b4GapPatternWeight 3 4 6 * 0 :=
      b4GapContribution_from_row 3 3 4 6 0 row_03_03_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_04_06

theorem row_03_03_04_07 : b4RowContribution (![3, 6, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 10, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 10 + 17 = 36
    decide
  have hzsq : (∑ i, (((![3, 6, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 434 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 10^2 + 17^2 = 434
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_04_07

theorem weighted_03_03_04_07 : b4RawGapContribution ![3, 3, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 4, 7] = b4GapPatternWeight 3 4 7 * 0 :=
      b4GapContribution_from_row 3 3 4 7 0 row_03_03_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_04_07

theorem row_03_03_04_08 : b4RowContribution (![3, 6, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 10, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 10 + 18 = 37
    decide
  have hzsq : (∑ i, (((![3, 6, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 469 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 10^2 + 18^2 = 469
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_04_08

theorem weighted_03_03_04_08 : b4RawGapContribution ![3, 3, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 4, 8] = b4GapPatternWeight 3 4 8 * 0 :=
      b4GapContribution_from_row 3 3 4 8 0 row_03_03_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_04_08

def dvalues_03_03_04 : Fin 9 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_03_04

theorem dblock_03_03_04 : b4GapPatternDBlock 3 3 4 = 0 := by
  calc
    b4GapPatternDBlock 3 3 4 = ∑ d : Fin 9, dvalues_03_03_04 d := by
      apply b4GapDBlock_of_rows 3 3 4 dvalues_03_03_04
      intro d
      fin_cases d
      · exact weighted_03_03_04_00
      · exact weighted_03_03_04_01
      · exact weighted_03_03_04_02
      · exact weighted_03_03_04_03
      · exact weighted_03_03_04_04
      · exact weighted_03_03_04_05
      · exact weighted_03_03_04_06
      · exact weighted_03_03_04_07
      · exact weighted_03_03_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_03_04

end Paper7MomentGapNumeric
