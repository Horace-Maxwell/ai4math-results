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

theorem row_02_04_03_00 : b4RowContribution (![2, 6, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 9, 9] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 9 + 9 = 26
    decide
  have hzsq : (∑ i, (((![2, 6, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 202 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 9^2 + 9^2 = 202
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_03_00

theorem weighted_02_04_03_00 : b4RawGapContribution ![2, 4, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 3, 0] = b4GapPatternWeight 4 3 0 * 0 :=
      b4GapContribution_from_row 2 4 3 0 0 row_02_04_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_03_00

theorem row_02_04_03_01 : b4RowContribution (![2, 6, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 9, 10] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 9 + 10 = 27
    decide
  have hzsq : (∑ i, (((![2, 6, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 221 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 9^2 + 10^2 = 221
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_03_01

theorem weighted_02_04_03_01 : b4RawGapContribution ![2, 4, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 3, 1] = b4GapPatternWeight 4 3 1 * 0 :=
      b4GapContribution_from_row 2 4 3 1 0 row_02_04_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_03_01

theorem row_02_04_03_02 : b4RowContribution (![2, 6, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 9, 11] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 9 + 11 = 28
    decide
  have hzsq : (∑ i, (((![2, 6, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 242 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 9^2 + 11^2 = 242
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_03_02

theorem weighted_02_04_03_02 : b4RawGapContribution ![2, 4, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 3, 2] = b4GapPatternWeight 4 3 2 * 0 :=
      b4GapContribution_from_row 2 4 3 2 0 row_02_04_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_03_02

theorem row_02_04_03_03 : b4RowContribution (![2, 6, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 9, 12] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 9 + 12 = 29
    decide
  have hzsq : (∑ i, (((![2, 6, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 265 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 9^2 + 12^2 = 265
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_03_03

theorem weighted_02_04_03_03 : b4RawGapContribution ![2, 4, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 3, 3] = b4GapPatternWeight 4 3 3 * 0 :=
      b4GapContribution_from_row 2 4 3 3 0 row_02_04_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_03_03

theorem row_02_04_03_04 : b4RowContribution (![2, 6, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 9, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 9 + 13 = 30
    decide
  have hzsq : (∑ i, (((![2, 6, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 290 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 9^2 + 13^2 = 290
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_03_04

theorem weighted_02_04_03_04 : b4RawGapContribution ![2, 4, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 3, 4] = b4GapPatternWeight 4 3 4 * 0 :=
      b4GapContribution_from_row 2 4 3 4 0 row_02_04_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_03_04

theorem row_02_04_03_05 : b4RowContribution (![2, 6, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 9, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 9 + 14 = 31
    decide
  have hzsq : (∑ i, (((![2, 6, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 317 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 9^2 + 14^2 = 317
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_03_05

theorem weighted_02_04_03_05 : b4RawGapContribution ![2, 4, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 3, 5] = b4GapPatternWeight 4 3 5 * 0 :=
      b4GapContribution_from_row 2 4 3 5 0 row_02_04_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_03_05

theorem row_02_04_03_06 : b4RowContribution (![2, 6, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 9, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 9 + 15 = 32
    decide
  have hzsq : (∑ i, (((![2, 6, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 346 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 9^2 + 15^2 = 346
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_03_06

theorem weighted_02_04_03_06 : b4RawGapContribution ![2, 4, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 3, 6] = b4GapPatternWeight 4 3 6 * 0 :=
      b4GapContribution_from_row 2 4 3 6 0 row_02_04_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_03_06

theorem row_02_04_03_07 : b4RowContribution (![2, 6, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 9, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 9 + 16 = 33
    decide
  have hzsq : (∑ i, (((![2, 6, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 377 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 9^2 + 16^2 = 377
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_03_07

theorem weighted_02_04_03_07 : b4RawGapContribution ![2, 4, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 3, 7] = b4GapPatternWeight 4 3 7 * 0 :=
      b4GapContribution_from_row 2 4 3 7 0 row_02_04_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_03_07

theorem row_02_04_03_08 : b4RowContribution (![2, 6, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 9, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 9 + 17 = 34
    decide
  have hzsq : (∑ i, (((![2, 6, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 410 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 9^2 + 17^2 = 410
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_03_08

theorem weighted_02_04_03_08 : b4RawGapContribution ![2, 4, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 3, 8] = b4GapPatternWeight 4 3 8 * 0 :=
      b4GapContribution_from_row 2 4 3 8 0 row_02_04_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_03_08

theorem row_02_04_03_09 : b4RowContribution (![2, 6, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 9, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 9 + 18 = 35
    decide
  have hzsq : (∑ i, (((![2, 6, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 445 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 9^2 + 18^2 = 445
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_03_09

theorem weighted_02_04_03_09 : b4RawGapContribution ![2, 4, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 3, 9] = b4GapPatternWeight 4 3 9 * 0 :=
      b4GapContribution_from_row 2 4 3 9 0 row_02_04_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_03_09

theorem row_02_04_03_10 : b4RowContribution (![2, 6, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 9, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 9 + 19 = 36
    decide
  have hzsq : (∑ i, (((![2, 6, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 482 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 9^2 + 19^2 = 482
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_03_10

theorem weighted_02_04_03_10 : b4RawGapContribution ![2, 4, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 3, 10] = b4GapPatternWeight 4 3 10 * 0 :=
      b4GapContribution_from_row 2 4 3 10 0 row_02_04_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_03_10

theorem row_02_04_03_11 : b4RowContribution (![2, 6, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 9, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 9 + 20 = 37
    decide
  have hzsq : (∑ i, (((![2, 6, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 521 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 9^2 + 20^2 = 521
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_03_11

theorem weighted_02_04_03_11 : b4RawGapContribution ![2, 4, 3, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 3, 11] = b4GapPatternWeight 4 3 11 * 0 :=
      b4GapContribution_from_row 2 4 3 11 0 row_02_04_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_03_11

def dvalues_02_04_03 : Fin 12 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_04_03

theorem dblock_02_04_03 : b4GapPatternDBlock 2 4 3 = 0 := by
  calc
    b4GapPatternDBlock 2 4 3 = ∑ d : Fin 12, dvalues_02_04_03 d := by
      apply b4GapDBlock_of_rows 2 4 3 dvalues_02_04_03
      intro d
      fin_cases d
      · exact weighted_02_04_03_00
      · exact weighted_02_04_03_01
      · exact weighted_02_04_03_02
      · exact weighted_02_04_03_03
      · exact weighted_02_04_03_04
      · exact weighted_02_04_03_05
      · exact weighted_02_04_03_06
      · exact weighted_02_04_03_07
      · exact weighted_02_04_03_08
      · exact weighted_02_04_03_09
      · exact weighted_02_04_03_10
      · exact weighted_02_04_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_04_03

end Paper7MomentGapNumeric
