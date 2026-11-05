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

theorem row_01_05_02_00 : b4RowContribution (![1, 6, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 8, 8] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 8 + 8 = 23
    decide
  have hzsq : (∑ i, (((![1, 6, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 165 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 8^2 + 8^2 = 165
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_02_00

theorem weighted_01_05_02_00 : b4RawGapContribution ![1, 5, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 2, 0] = b4GapPatternWeight 5 2 0 * 0 :=
      b4GapContribution_from_row 1 5 2 0 0 row_01_05_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_00

theorem row_01_05_02_01 : b4RowContribution (![1, 6, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 8, 9] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 8 + 9 = 24
    decide
  have hzsq : (∑ i, (((![1, 6, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 182 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 8^2 + 9^2 = 182
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_02_01

theorem weighted_01_05_02_01 : b4RawGapContribution ![1, 5, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 2, 1] = b4GapPatternWeight 5 2 1 * 0 :=
      b4GapContribution_from_row 1 5 2 1 0 row_01_05_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_01

theorem row_01_05_02_02 : b4RowContribution (![1, 6, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 8, 10] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 8 + 10 = 25
    decide
  have hzsq : (∑ i, (((![1, 6, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 201 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 8^2 + 10^2 = 201
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_02_02

theorem weighted_01_05_02_02 : b4RawGapContribution ![1, 5, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 2, 2] = b4GapPatternWeight 5 2 2 * 0 :=
      b4GapContribution_from_row 1 5 2 2 0 row_01_05_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_02

theorem row_01_05_02_03 : b4RowContribution (![1, 6, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 8, 11] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 8 + 11 = 26
    decide
  have hzsq : (∑ i, (((![1, 6, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 222 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 8^2 + 11^2 = 222
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_02_03

theorem weighted_01_05_02_03 : b4RawGapContribution ![1, 5, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 2, 3] = b4GapPatternWeight 5 2 3 * 0 :=
      b4GapContribution_from_row 1 5 2 3 0 row_01_05_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_03

theorem row_01_05_02_04 : b4RowContribution (![1, 6, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 8, 12] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 8 + 12 = 27
    decide
  have hzsq : (∑ i, (((![1, 6, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 245 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 8^2 + 12^2 = 245
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_02_04

theorem weighted_01_05_02_04 : b4RawGapContribution ![1, 5, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 2, 4] = b4GapPatternWeight 5 2 4 * 0 :=
      b4GapContribution_from_row 1 5 2 4 0 row_01_05_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_04

def layers_01_05_02_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 14, 14, 13, 11, 9, 7, 5, 3, 1, 0, 0, 0], ![1, 4, 9, 16, 25, 36, 49, 63, 77, 90, 101, 110, 117, 122, 124, 122, 117, 110, 101]]
#print axioms Paper7MomentGapNumeric.layers_01_05_02_05

theorem cells_01_05_02_05 : QTableValid (![1, 6, 8, 13] : Fin 4 → ℕ) layers_01_05_02_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_05_02_05

theorem valid_01_05_02_05 :
    SparseRowValid (![1, 6, 8, 13] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_05_02_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 6, 8, 13] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 1 + 6 + 8 + 13 = 28
      decide
    have hzsq : (∑ i, (((![1, 6, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 6^2 + 8^2 + 13^2 = 270
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_05_02_05
#print axioms Paper7MomentGapNumeric.valid_01_05_02_05

def qvalues_01_05_02_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 90, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_05_02_05

theorem row_01_05_02_05 : b4RowContribution (![1, 6, 8, 13] : Fin 4 → ℕ) = 90 := by
  calc
    b4RowContribution (![1, 6, 8, 13] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_05_02_05) :=
      sparseRow_sound (![1, 6, 8, 13] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_05_02_05) valid_01_05_02_05
    _ = 90 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_05_02_05 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 90 := by decide
#print axioms Paper7MomentGapNumeric.row_01_05_02_05

theorem weighted_01_05_02_05 : b4RawGapContribution ![1, 5, 2, 5] = 2160 := by
  calc
    b4RawGapContribution ![1, 5, 2, 5] = b4GapPatternWeight 5 2 5 * 90 :=
      b4GapContribution_from_row 1 5 2 5 90 row_01_05_02_05
    _ = 2160 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_05

theorem row_01_05_02_06 : b4RowContribution (![1, 6, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 8, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 8 + 14 = 29
    decide
  have hzsq : (∑ i, (((![1, 6, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 297 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 8^2 + 14^2 = 297
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_02_06

theorem weighted_01_05_02_06 : b4RawGapContribution ![1, 5, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 2, 6] = b4GapPatternWeight 5 2 6 * 0 :=
      b4GapContribution_from_row 1 5 2 6 0 row_01_05_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_06

theorem row_01_05_02_07 : b4RowContribution (![1, 6, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 8, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 8 + 15 = 30
    decide
  have hzsq : (∑ i, (((![1, 6, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 326 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 8^2 + 15^2 = 326
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_02_07

theorem weighted_01_05_02_07 : b4RawGapContribution ![1, 5, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 2, 7] = b4GapPatternWeight 5 2 7 * 0 :=
      b4GapContribution_from_row 1 5 2 7 0 row_01_05_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_07

theorem row_01_05_02_08 : b4RowContribution (![1, 6, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 8, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 8 + 16 = 31
    decide
  have hzsq : (∑ i, (((![1, 6, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 357 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 8^2 + 16^2 = 357
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_02_08

theorem weighted_01_05_02_08 : b4RawGapContribution ![1, 5, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 2, 8] = b4GapPatternWeight 5 2 8 * 0 :=
      b4GapContribution_from_row 1 5 2 8 0 row_01_05_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_08

theorem row_01_05_02_09 : b4RowContribution (![1, 6, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 8, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 8 + 17 = 32
    decide
  have hzsq : (∑ i, (((![1, 6, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 8^2 + 17^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_02_09

theorem weighted_01_05_02_09 : b4RawGapContribution ![1, 5, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 2, 9] = b4GapPatternWeight 5 2 9 * 0 :=
      b4GapContribution_from_row 1 5 2 9 0 row_01_05_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_09

theorem row_01_05_02_10 : b4RowContribution (![1, 6, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 8, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 8 + 18 = 33
    decide
  have hzsq : (∑ i, (((![1, 6, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 425 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 8^2 + 18^2 = 425
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_02_10

theorem weighted_01_05_02_10 : b4RawGapContribution ![1, 5, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 2, 10] = b4GapPatternWeight 5 2 10 * 0 :=
      b4GapContribution_from_row 1 5 2 10 0 row_01_05_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_10

theorem row_01_05_02_11 : b4RowContribution (![1, 6, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 8, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 8 + 19 = 34
    decide
  have hzsq : (∑ i, (((![1, 6, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 462 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 8^2 + 19^2 = 462
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_02_11

theorem weighted_01_05_02_11 : b4RawGapContribution ![1, 5, 2, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 2, 11] = b4GapPatternWeight 5 2 11 * 0 :=
      b4GapContribution_from_row 1 5 2 11 0 row_01_05_02_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_11

theorem row_01_05_02_12 : b4RowContribution (![1, 6, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 8, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 8 + 20 = 35
    decide
  have hzsq : (∑ i, (((![1, 6, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 501 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 8^2 + 20^2 = 501
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_02_12

theorem weighted_01_05_02_12 : b4RawGapContribution ![1, 5, 2, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 2, 12] = b4GapPatternWeight 5 2 12 * 0 :=
      b4GapContribution_from_row 1 5 2 12 0 row_01_05_02_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_12

theorem row_01_05_02_13 : b4RowContribution (![1, 6, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 8, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 8 + 21 = 36
    decide
  have hzsq : (∑ i, (((![1, 6, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 542 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 8^2 + 21^2 = 542
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_02_13

theorem weighted_01_05_02_13 : b4RawGapContribution ![1, 5, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 2, 13] = b4GapPatternWeight 5 2 13 * 0 :=
      b4GapContribution_from_row 1 5 2 13 0 row_01_05_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_13

theorem row_01_05_02_14 : b4RowContribution (![1, 6, 8, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 8, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 8 + 22 = 37
    decide
  have hzsq : (∑ i, (((![1, 6, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 585 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 8^2 + 22^2 = 585
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_02_14

theorem weighted_01_05_02_14 : b4RawGapContribution ![1, 5, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 2, 14] = b4GapPatternWeight 5 2 14 * 0 :=
      b4GapContribution_from_row 1 5 2 14 0 row_01_05_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_02_14

def dvalues_01_05_02 : Fin 15 → ℕ := ![0, 0, 0, 0, 0, 2160, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_05_02

theorem dblock_01_05_02 : b4GapPatternDBlock 1 5 2 = 2160 := by
  calc
    b4GapPatternDBlock 1 5 2 = ∑ d : Fin 15, dvalues_01_05_02 d := by
      apply b4GapDBlock_of_rows 1 5 2 dvalues_01_05_02
      intro d
      fin_cases d
      · exact weighted_01_05_02_00
      · exact weighted_01_05_02_01
      · exact weighted_01_05_02_02
      · exact weighted_01_05_02_03
      · exact weighted_01_05_02_04
      · exact weighted_01_05_02_05
      · exact weighted_01_05_02_06
      · exact weighted_01_05_02_07
      · exact weighted_01_05_02_08
      · exact weighted_01_05_02_09
      · exact weighted_01_05_02_10
      · exact weighted_01_05_02_11
      · exact weighted_01_05_02_12
      · exact weighted_01_05_02_13
      · exact weighted_01_05_02_14
    _ = 2160 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_05_02

end Paper7MomentGapNumeric
