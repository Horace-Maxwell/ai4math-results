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

theorem row_01_00_12_00 : b4RowContribution (![1, 1, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 13, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 13 + 13 = 28
    decide
  have hzsq : (∑ i, (((![1, 1, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 340 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 13^2 + 13^2 = 340
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_12_00

theorem weighted_01_00_12_00 : b4RawGapContribution ![1, 0, 12, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 12, 0] = b4GapPatternWeight 0 12 0 * 0 :=
      b4GapContribution_from_row 1 0 12 0 0 row_01_00_12_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_12_00

theorem row_01_00_12_01 : b4RowContribution (![1, 1, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 13, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 13 + 14 = 29
    decide
  have hzsq : (∑ i, (((![1, 1, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 367 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 13^2 + 14^2 = 367
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_12_01

theorem weighted_01_00_12_01 : b4RawGapContribution ![1, 0, 12, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 12, 1] = b4GapPatternWeight 0 12 1 * 0 :=
      b4GapContribution_from_row 1 0 12 1 0 row_01_00_12_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_12_01

theorem row_01_00_12_02 : b4RowContribution (![1, 1, 13, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 13, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 13 + 15 = 30
    decide
  have hzsq : (∑ i, (((![1, 1, 13, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 396 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 13^2 + 15^2 = 396
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_12_02

theorem weighted_01_00_12_02 : b4RawGapContribution ![1, 0, 12, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 12, 2] = b4GapPatternWeight 0 12 2 * 0 :=
      b4GapContribution_from_row 1 0 12 2 0 row_01_00_12_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_12_02

theorem row_01_00_12_03 : b4RowContribution (![1, 1, 13, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 13, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 13 + 16 = 31
    decide
  have hzsq : (∑ i, (((![1, 1, 13, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 427 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 13^2 + 16^2 = 427
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_12_03

theorem weighted_01_00_12_03 : b4RawGapContribution ![1, 0, 12, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 12, 3] = b4GapPatternWeight 0 12 3 * 0 :=
      b4GapContribution_from_row 1 0 12 3 0 row_01_00_12_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_12_03

theorem row_01_00_12_04 : b4RowContribution (![1, 1, 13, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 13, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 13 + 17 = 32
    decide
  have hzsq : (∑ i, (((![1, 1, 13, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 460 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 13^2 + 17^2 = 460
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_12_04

theorem weighted_01_00_12_04 : b4RawGapContribution ![1, 0, 12, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 12, 4] = b4GapPatternWeight 0 12 4 * 0 :=
      b4GapContribution_from_row 1 0 12 4 0 row_01_00_12_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_12_04

theorem row_01_00_12_05 : b4RowContribution (![1, 1, 13, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 13, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 13 + 18 = 33
    decide
  have hzsq : (∑ i, (((![1, 1, 13, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 495 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 13^2 + 18^2 = 495
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_12_05

theorem weighted_01_00_12_05 : b4RawGapContribution ![1, 0, 12, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 12, 5] = b4GapPatternWeight 0 12 5 * 0 :=
      b4GapContribution_from_row 1 0 12 5 0 row_01_00_12_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_12_05

theorem row_01_00_12_06 : b4RowContribution (![1, 1, 13, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 13, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 13 + 19 = 34
    decide
  have hzsq : (∑ i, (((![1, 1, 13, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 532 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 13^2 + 19^2 = 532
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_12_06

theorem weighted_01_00_12_06 : b4RawGapContribution ![1, 0, 12, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 12, 6] = b4GapPatternWeight 0 12 6 * 0 :=
      b4GapContribution_from_row 1 0 12 6 0 row_01_00_12_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_12_06

theorem row_01_00_12_07 : b4RowContribution (![1, 1, 13, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 13, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 13 + 20 = 35
    decide
  have hzsq : (∑ i, (((![1, 1, 13, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 571 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 13^2 + 20^2 = 571
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_12_07

theorem weighted_01_00_12_07 : b4RawGapContribution ![1, 0, 12, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 12, 7] = b4GapPatternWeight 0 12 7 * 0 :=
      b4GapContribution_from_row 1 0 12 7 0 row_01_00_12_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_12_07

theorem row_01_00_12_08 : b4RowContribution (![1, 1, 13, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 13, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 13 + 21 = 36
    decide
  have hzsq : (∑ i, (((![1, 1, 13, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 612 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 13^2 + 21^2 = 612
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_12_08

theorem weighted_01_00_12_08 : b4RawGapContribution ![1, 0, 12, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 12, 8] = b4GapPatternWeight 0 12 8 * 0 :=
      b4GapContribution_from_row 1 0 12 8 0 row_01_00_12_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_12_08

theorem row_01_00_12_09 : b4RowContribution (![1, 1, 13, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 13, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 13 + 22 = 37
    decide
  have hzsq : (∑ i, (((![1, 1, 13, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 655 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 13^2 + 22^2 = 655
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_12_09

theorem weighted_01_00_12_09 : b4RawGapContribution ![1, 0, 12, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 12, 9] = b4GapPatternWeight 0 12 9 * 0 :=
      b4GapContribution_from_row 1 0 12 9 0 row_01_00_12_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_12_09

def dvalues_01_00_12 : Fin 10 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_00_12

theorem dblock_01_00_12 : b4GapPatternDBlock 1 0 12 = 0 := by
  calc
    b4GapPatternDBlock 1 0 12 = ∑ d : Fin 10, dvalues_01_00_12 d := by
      apply b4GapDBlock_of_rows 1 0 12 dvalues_01_00_12
      intro d
      fin_cases d
      · exact weighted_01_00_12_00
      · exact weighted_01_00_12_01
      · exact weighted_01_00_12_02
      · exact weighted_01_00_12_03
      · exact weighted_01_00_12_04
      · exact weighted_01_00_12_05
      · exact weighted_01_00_12_06
      · exact weighted_01_00_12_07
      · exact weighted_01_00_12_08
      · exact weighted_01_00_12_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_00_12

end Paper7MomentGapNumeric
