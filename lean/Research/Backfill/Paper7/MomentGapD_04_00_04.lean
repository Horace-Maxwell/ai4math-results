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

theorem row_04_00_04_00 : b4RowContribution (![4, 4, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 8, 8] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 8 + 8 = 24
    decide
  have hzsq : (∑ i, (((![4, 4, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 160 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 8^2 + 8^2 = 160
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_04_00

theorem weighted_04_00_04_00 : b4RawGapContribution ![4, 0, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 4, 0] = b4GapPatternWeight 0 4 0 * 0 :=
      b4GapContribution_from_row 4 0 4 0 0 row_04_00_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_04_00

theorem row_04_00_04_01 : b4RowContribution (![4, 4, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 8, 9] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 8 + 9 = 25
    decide
  have hzsq : (∑ i, (((![4, 4, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 177 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 8^2 + 9^2 = 177
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_04_01

theorem weighted_04_00_04_01 : b4RawGapContribution ![4, 0, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 4, 1] = b4GapPatternWeight 0 4 1 * 0 :=
      b4GapContribution_from_row 4 0 4 1 0 row_04_00_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_04_01

theorem row_04_00_04_02 : b4RowContribution (![4, 4, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 8, 10] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 8 + 10 = 26
    decide
  have hzsq : (∑ i, (((![4, 4, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 196 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 8^2 + 10^2 = 196
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_04_02

theorem weighted_04_00_04_02 : b4RawGapContribution ![4, 0, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 4, 2] = b4GapPatternWeight 0 4 2 * 0 :=
      b4GapContribution_from_row 4 0 4 2 0 row_04_00_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_04_02

theorem row_04_00_04_03 : b4RowContribution (![4, 4, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 8, 11] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 8 + 11 = 27
    decide
  have hzsq : (∑ i, (((![4, 4, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 217 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 8^2 + 11^2 = 217
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_04_03

theorem weighted_04_00_04_03 : b4RawGapContribution ![4, 0, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 4, 3] = b4GapPatternWeight 0 4 3 * 0 :=
      b4GapContribution_from_row 4 0 4 3 0 row_04_00_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_04_03

theorem row_04_00_04_04 : b4RowContribution (![4, 4, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 8, 12] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 8 + 12 = 28
    decide
  have hzsq : (∑ i, (((![4, 4, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 240 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 8^2 + 12^2 = 240
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_04_04

theorem weighted_04_00_04_04 : b4RawGapContribution ![4, 0, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 4, 4] = b4GapPatternWeight 0 4 4 * 0 :=
      b4GapContribution_from_row 4 0 4 4 0 row_04_00_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_04_04

theorem row_04_00_04_05 : b4RowContribution (![4, 4, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 8, 13] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 8 + 13 = 29
    decide
  have hzsq : (∑ i, (((![4, 4, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 265 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 8^2 + 13^2 = 265
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_04_05

theorem weighted_04_00_04_05 : b4RawGapContribution ![4, 0, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 4, 5] = b4GapPatternWeight 0 4 5 * 0 :=
      b4GapContribution_from_row 4 0 4 5 0 row_04_00_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_04_05

theorem row_04_00_04_06 : b4RowContribution (![4, 4, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 8, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 8 + 14 = 30
    decide
  have hzsq : (∑ i, (((![4, 4, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 292 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 8^2 + 14^2 = 292
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_04_06

theorem weighted_04_00_04_06 : b4RawGapContribution ![4, 0, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 4, 6] = b4GapPatternWeight 0 4 6 * 0 :=
      b4GapContribution_from_row 4 0 4 6 0 row_04_00_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_04_06

theorem row_04_00_04_07 : b4RowContribution (![4, 4, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 8, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 8 + 15 = 31
    decide
  have hzsq : (∑ i, (((![4, 4, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 321 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 8^2 + 15^2 = 321
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_04_07

theorem weighted_04_00_04_07 : b4RawGapContribution ![4, 0, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 4, 7] = b4GapPatternWeight 0 4 7 * 0 :=
      b4GapContribution_from_row 4 0 4 7 0 row_04_00_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_04_07

theorem row_04_00_04_08 : b4RowContribution (![4, 4, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 8, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 8 + 16 = 32
    decide
  have hzsq : (∑ i, (((![4, 4, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 352 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 8^2 + 16^2 = 352
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_04_08

theorem weighted_04_00_04_08 : b4RawGapContribution ![4, 0, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 4, 8] = b4GapPatternWeight 0 4 8 * 0 :=
      b4GapContribution_from_row 4 0 4 8 0 row_04_00_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_04_08

theorem row_04_00_04_09 : b4RowContribution (![4, 4, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 8, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 8 + 17 = 33
    decide
  have hzsq : (∑ i, (((![4, 4, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 385 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 8^2 + 17^2 = 385
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_04_09

theorem weighted_04_00_04_09 : b4RawGapContribution ![4, 0, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 4, 9] = b4GapPatternWeight 0 4 9 * 0 :=
      b4GapContribution_from_row 4 0 4 9 0 row_04_00_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_04_09

theorem row_04_00_04_10 : b4RowContribution (![4, 4, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 8, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 8 + 18 = 34
    decide
  have hzsq : (∑ i, (((![4, 4, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 420 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 8^2 + 18^2 = 420
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_04_10

theorem weighted_04_00_04_10 : b4RawGapContribution ![4, 0, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 4, 10] = b4GapPatternWeight 0 4 10 * 0 :=
      b4GapContribution_from_row 4 0 4 10 0 row_04_00_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_04_10

theorem row_04_00_04_11 : b4RowContribution (![4, 4, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 8, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 8 + 19 = 35
    decide
  have hzsq : (∑ i, (((![4, 4, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 457 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 8^2 + 19^2 = 457
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_04_11

theorem weighted_04_00_04_11 : b4RawGapContribution ![4, 0, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 4, 11] = b4GapPatternWeight 0 4 11 * 0 :=
      b4GapContribution_from_row 4 0 4 11 0 row_04_00_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_04_11

theorem row_04_00_04_12 : b4RowContribution (![4, 4, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 8, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 8 + 20 = 36
    decide
  have hzsq : (∑ i, (((![4, 4, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 496 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 8^2 + 20^2 = 496
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_04_12

theorem weighted_04_00_04_12 : b4RawGapContribution ![4, 0, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 4, 12] = b4GapPatternWeight 0 4 12 * 0 :=
      b4GapContribution_from_row 4 0 4 12 0 row_04_00_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_04_12

theorem row_04_00_04_13 : b4RowContribution (![4, 4, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 8, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 8 + 21 = 37
    decide
  have hzsq : (∑ i, (((![4, 4, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 537 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 8^2 + 21^2 = 537
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_04_13

theorem weighted_04_00_04_13 : b4RawGapContribution ![4, 0, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 4, 13] = b4GapPatternWeight 0 4 13 * 0 :=
      b4GapContribution_from_row 4 0 4 13 0 row_04_00_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_04_13

def dvalues_04_00_04 : Fin 14 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_00_04

theorem dblock_04_00_04 : b4GapPatternDBlock 4 0 4 = 0 := by
  calc
    b4GapPatternDBlock 4 0 4 = ∑ d : Fin 14, dvalues_04_00_04 d := by
      apply b4GapDBlock_of_rows 4 0 4 dvalues_04_00_04
      intro d
      fin_cases d
      · exact weighted_04_00_04_00
      · exact weighted_04_00_04_01
      · exact weighted_04_00_04_02
      · exact weighted_04_00_04_03
      · exact weighted_04_00_04_04
      · exact weighted_04_00_04_05
      · exact weighted_04_00_04_06
      · exact weighted_04_00_04_07
      · exact weighted_04_00_04_08
      · exact weighted_04_00_04_09
      · exact weighted_04_00_04_10
      · exact weighted_04_00_04_11
      · exact weighted_04_00_04_12
      · exact weighted_04_00_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_00_04

end Paper7MomentGapNumeric
