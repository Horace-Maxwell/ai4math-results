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

theorem row_04_03_03_00 : b4RowContribution (![4, 7, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 10, 10] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 10 + 10 = 31
    decide
  have hzsq : (∑ i, (((![4, 7, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 265 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 10^2 + 10^2 = 265
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_03_00

theorem weighted_04_03_03_00 : b4RawGapContribution ![4, 3, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 3, 0] = b4GapPatternWeight 3 3 0 * 0 :=
      b4GapContribution_from_row 4 3 3 0 0 row_04_03_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_03_00

theorem row_04_03_03_01 : b4RowContribution (![4, 7, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 10, 11] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 10 + 11 = 32
    decide
  have hzsq : (∑ i, (((![4, 7, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 286 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 10^2 + 11^2 = 286
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_03_01

theorem weighted_04_03_03_01 : b4RawGapContribution ![4, 3, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 3, 1] = b4GapPatternWeight 3 3 1 * 0 :=
      b4GapContribution_from_row 4 3 3 1 0 row_04_03_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_03_01

theorem row_04_03_03_02 : b4RowContribution (![4, 7, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 10, 12] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 10 + 12 = 33
    decide
  have hzsq : (∑ i, (((![4, 7, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 309 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 10^2 + 12^2 = 309
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_03_02

theorem weighted_04_03_03_02 : b4RawGapContribution ![4, 3, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 3, 2] = b4GapPatternWeight 3 3 2 * 0 :=
      b4GapContribution_from_row 4 3 3 2 0 row_04_03_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_03_02

theorem row_04_03_03_03 : b4RowContribution (![4, 7, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 10, 13] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 10 + 13 = 34
    decide
  have hzsq : (∑ i, (((![4, 7, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 334 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 10^2 + 13^2 = 334
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_03_03

theorem weighted_04_03_03_03 : b4RawGapContribution ![4, 3, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 3, 3] = b4GapPatternWeight 3 3 3 * 0 :=
      b4GapContribution_from_row 4 3 3 3 0 row_04_03_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_03_03

theorem row_04_03_03_04 : b4RowContribution (![4, 7, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 10, 14] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 10 + 14 = 35
    decide
  have hzsq : (∑ i, (((![4, 7, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 361 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 10^2 + 14^2 = 361
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_03_04

theorem weighted_04_03_03_04 : b4RawGapContribution ![4, 3, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 3, 4] = b4GapPatternWeight 3 3 4 * 0 :=
      b4GapContribution_from_row 4 3 3 4 0 row_04_03_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_03_04

theorem row_04_03_03_05 : b4RowContribution (![4, 7, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 10, 15] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 10 + 15 = 36
    decide
  have hzsq : (∑ i, (((![4, 7, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 10^2 + 15^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_03_05

theorem weighted_04_03_03_05 : b4RawGapContribution ![4, 3, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 3, 5] = b4GapPatternWeight 3 3 5 * 0 :=
      b4GapContribution_from_row 4 3 3 5 0 row_04_03_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_03_05

theorem row_04_03_03_06 : b4RowContribution (![4, 7, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 10, 16] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 10 + 16 = 37
    decide
  have hzsq : (∑ i, (((![4, 7, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 421 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 10^2 + 16^2 = 421
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_03_06

theorem weighted_04_03_03_06 : b4RawGapContribution ![4, 3, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 3, 6] = b4GapPatternWeight 3 3 6 * 0 :=
      b4GapContribution_from_row 4 3 3 6 0 row_04_03_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_03_06

def dvalues_04_03_03 : Fin 7 → ℕ := ![0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_03_03

theorem dblock_04_03_03 : b4GapPatternDBlock 4 3 3 = 0 := by
  calc
    b4GapPatternDBlock 4 3 3 = ∑ d : Fin 7, dvalues_04_03_03 d := by
      apply b4GapDBlock_of_rows 4 3 3 dvalues_04_03_03
      intro d
      fin_cases d
      · exact weighted_04_03_03_00
      · exact weighted_04_03_03_01
      · exact weighted_04_03_03_02
      · exact weighted_04_03_03_03
      · exact weighted_04_03_03_04
      · exact weighted_04_03_03_05
      · exact weighted_04_03_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_03_03

end Paper7MomentGapNumeric
