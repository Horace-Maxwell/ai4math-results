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

theorem row_05_01_00_00 : b4RowContribution (![5, 6, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 6] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 6 = 23
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 133 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 6^2 = 133
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_00

theorem weighted_05_01_00_00 : b4RawGapContribution ![5, 1, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 0] = b4GapPatternWeight 1 0 0 * 0 :=
      b4GapContribution_from_row 5 1 0 0 0 row_05_01_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_00

theorem row_05_01_00_01 : b4RowContribution (![5, 6, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 7] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 7 = 24
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 146 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 7^2 = 146
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_01

theorem weighted_05_01_00_01 : b4RawGapContribution ![5, 1, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 1] = b4GapPatternWeight 1 0 1 * 0 :=
      b4GapContribution_from_row 5 1 0 1 0 row_05_01_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_01

theorem row_05_01_00_02 : b4RowContribution (![5, 6, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 8] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 8 = 25
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 161 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 8^2 = 161
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_02

theorem weighted_05_01_00_02 : b4RawGapContribution ![5, 1, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 2] = b4GapPatternWeight 1 0 2 * 0 :=
      b4GapContribution_from_row 5 1 0 2 0 row_05_01_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_02

theorem row_05_01_00_03 : b4RowContribution (![5, 6, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 9] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 9 = 26
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 178 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 9^2 = 178
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_03

theorem weighted_05_01_00_03 : b4RawGapContribution ![5, 1, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 3] = b4GapPatternWeight 1 0 3 * 0 :=
      b4GapContribution_from_row 5 1 0 3 0 row_05_01_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_03

theorem row_05_01_00_04 : b4RowContribution (![5, 6, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 10] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 10 = 27
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 197 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 10^2 = 197
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_04

theorem weighted_05_01_00_04 : b4RawGapContribution ![5, 1, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 4] = b4GapPatternWeight 1 0 4 * 0 :=
      b4GapContribution_from_row 5 1 0 4 0 row_05_01_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_04

theorem row_05_01_00_05 : b4RowContribution (![5, 6, 6, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 11] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 11 = 28
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 218 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 11^2 = 218
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_05

theorem weighted_05_01_00_05 : b4RawGapContribution ![5, 1, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 5] = b4GapPatternWeight 1 0 5 * 0 :=
      b4GapContribution_from_row 5 1 0 5 0 row_05_01_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_05

theorem row_05_01_00_06 : b4RowContribution (![5, 6, 6, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 12] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 12 = 29
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 241 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 12^2 = 241
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_06

theorem weighted_05_01_00_06 : b4RawGapContribution ![5, 1, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 6] = b4GapPatternWeight 1 0 6 * 0 :=
      b4GapContribution_from_row 5 1 0 6 0 row_05_01_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_06

theorem row_05_01_00_07 : b4RowContribution (![5, 6, 6, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 13 = 30
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 266 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 13^2 = 266
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_07

theorem weighted_05_01_00_07 : b4RawGapContribution ![5, 1, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 7] = b4GapPatternWeight 1 0 7 * 0 :=
      b4GapContribution_from_row 5 1 0 7 0 row_05_01_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_07

theorem row_05_01_00_08 : b4RowContribution (![5, 6, 6, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 14 = 31
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 293 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 14^2 = 293
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_08

theorem weighted_05_01_00_08 : b4RawGapContribution ![5, 1, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 8] = b4GapPatternWeight 1 0 8 * 0 :=
      b4GapContribution_from_row 5 1 0 8 0 row_05_01_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_08

theorem row_05_01_00_09 : b4RowContribution (![5, 6, 6, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 15 = 32
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 322 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 15^2 = 322
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_09

theorem weighted_05_01_00_09 : b4RawGapContribution ![5, 1, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 9] = b4GapPatternWeight 1 0 9 * 0 :=
      b4GapContribution_from_row 5 1 0 9 0 row_05_01_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_09

theorem row_05_01_00_10 : b4RowContribution (![5, 6, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 16 = 33
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 353 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 16^2 = 353
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_10

theorem weighted_05_01_00_10 : b4RawGapContribution ![5, 1, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 10] = b4GapPatternWeight 1 0 10 * 0 :=
      b4GapContribution_from_row 5 1 0 10 0 row_05_01_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_10

theorem row_05_01_00_11 : b4RowContribution (![5, 6, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 17 = 34
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 386 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 17^2 = 386
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_11

theorem weighted_05_01_00_11 : b4RawGapContribution ![5, 1, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 11] = b4GapPatternWeight 1 0 11 * 0 :=
      b4GapContribution_from_row 5 1 0 11 0 row_05_01_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_11

theorem row_05_01_00_12 : b4RowContribution (![5, 6, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 18 = 35
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 421 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 18^2 = 421
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_12

theorem weighted_05_01_00_12 : b4RawGapContribution ![5, 1, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 12] = b4GapPatternWeight 1 0 12 * 0 :=
      b4GapContribution_from_row 5 1 0 12 0 row_05_01_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_12

theorem row_05_01_00_13 : b4RowContribution (![5, 6, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 19 = 36
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 458 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 19^2 = 458
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_13

theorem weighted_05_01_00_13 : b4RawGapContribution ![5, 1, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 13] = b4GapPatternWeight 1 0 13 * 0 :=
      b4GapContribution_from_row 5 1 0 13 0 row_05_01_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_13

theorem row_05_01_00_14 : b4RowContribution (![5, 6, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 6, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 6 + 20 = 37
    decide
  have hzsq : (∑ i, (((![5, 6, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 497 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 6^2 + 20^2 = 497
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_00_14

theorem weighted_05_01_00_14 : b4RawGapContribution ![5, 1, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 0, 14] = b4GapPatternWeight 1 0 14 * 0 :=
      b4GapContribution_from_row 5 1 0 14 0 row_05_01_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_00_14

def dvalues_05_01_00 : Fin 15 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_01_00

theorem dblock_05_01_00 : b4GapPatternDBlock 5 1 0 = 0 := by
  calc
    b4GapPatternDBlock 5 1 0 = ∑ d : Fin 15, dvalues_05_01_00 d := by
      apply b4GapDBlock_of_rows 5 1 0 dvalues_05_01_00
      intro d
      fin_cases d
      · exact weighted_05_01_00_00
      · exact weighted_05_01_00_01
      · exact weighted_05_01_00_02
      · exact weighted_05_01_00_03
      · exact weighted_05_01_00_04
      · exact weighted_05_01_00_05
      · exact weighted_05_01_00_06
      · exact weighted_05_01_00_07
      · exact weighted_05_01_00_08
      · exact weighted_05_01_00_09
      · exact weighted_05_01_00_10
      · exact weighted_05_01_00_11
      · exact weighted_05_01_00_12
      · exact weighted_05_01_00_13
      · exact weighted_05_01_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_01_00

end Paper7MomentGapNumeric
