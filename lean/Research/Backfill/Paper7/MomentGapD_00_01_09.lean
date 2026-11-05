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

theorem row_00_01_09_00 : b4RowContribution (![0, 1, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 10] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 10 = 21
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 201 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 10^2 = 201
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_00

theorem weighted_00_01_09_00 : b4RawGapContribution ![0, 1, 9, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 0] = b4GapPatternWeight 1 9 0 * 0 :=
      b4GapContribution_from_row 0 1 9 0 0 row_00_01_09_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_00

def layers_00_01_09_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 22, 21, 19, 17, 15, 13, 11, 9]]
#print axioms Paper7MomentGapNumeric.layers_00_01_09_01

theorem cells_00_01_09_01 : QTableValid (![0, 1, 10, 11] : Fin 4 → ℕ) layers_00_01_09_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_09_01

theorem valid_00_01_09_01 :
    SparseRowValid (![0, 1, 10, 11] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_01_09_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 10, 11] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 10 + 11 = 22
      decide
    have hzsq : (∑ i, (((![0, 1, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 222 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 10^2 + 11^2 = 222
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_09_01
#print axioms Paper7MomentGapNumeric.valid_00_01_09_01

def qvalues_00_01_09_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_09_01

theorem row_00_01_09_01 : b4RowContribution (![0, 1, 10, 11] : Fin 4 → ℕ) = 21 := by
  calc
    b4RowContribution (![0, 1, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_00_01_09_01) :=
      sparseRow_sound (![0, 1, 10, 11] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_01_09_01) valid_00_01_09_01
    _ = 21 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_09_01 Q := by
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
        _ = 21 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_09_01

theorem weighted_00_01_09_01 : b4RawGapContribution ![0, 1, 9, 1] = 504 := by
  calc
    b4RawGapContribution ![0, 1, 9, 1] = b4GapPatternWeight 1 9 1 * 21 :=
      b4GapContribution_from_row 0 1 9 1 21 row_00_01_09_01
    _ = 504 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_01

theorem row_00_01_09_02 : b4RowContribution (![0, 1, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 12] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 12 = 23
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 245 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 12^2 = 245
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_02

theorem weighted_00_01_09_02 : b4RawGapContribution ![0, 1, 9, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 2] = b4GapPatternWeight 1 9 2 * 0 :=
      b4GapContribution_from_row 0 1 9 2 0 row_00_01_09_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_02

theorem row_00_01_09_03 : b4RowContribution (![0, 1, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 13] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 13 = 24
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 13^2 = 270
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_03

theorem weighted_00_01_09_03 : b4RawGapContribution ![0, 1, 9, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 3] = b4GapPatternWeight 1 9 3 * 0 :=
      b4GapContribution_from_row 0 1 9 3 0 row_00_01_09_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_03

theorem row_00_01_09_04 : b4RowContribution (![0, 1, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 14] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 14 = 25
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 297 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 14^2 = 297
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_04

theorem weighted_00_01_09_04 : b4RawGapContribution ![0, 1, 9, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 4] = b4GapPatternWeight 1 9 4 * 0 :=
      b4GapContribution_from_row 0 1 9 4 0 row_00_01_09_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_04

theorem row_00_01_09_05 : b4RowContribution (![0, 1, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 15] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 15 = 26
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 326 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 15^2 = 326
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_05

theorem weighted_00_01_09_05 : b4RawGapContribution ![0, 1, 9, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 5] = b4GapPatternWeight 1 9 5 * 0 :=
      b4GapContribution_from_row 0 1 9 5 0 row_00_01_09_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_05

theorem row_00_01_09_06 : b4RowContribution (![0, 1, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 16] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 16 = 27
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 357 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 16^2 = 357
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_06

theorem weighted_00_01_09_06 : b4RawGapContribution ![0, 1, 9, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 6] = b4GapPatternWeight 1 9 6 * 0 :=
      b4GapContribution_from_row 0 1 9 6 0 row_00_01_09_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_06

theorem row_00_01_09_07 : b4RowContribution (![0, 1, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 17] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 17 = 28
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 17^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_07

theorem weighted_00_01_09_07 : b4RawGapContribution ![0, 1, 9, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 7] = b4GapPatternWeight 1 9 7 * 0 :=
      b4GapContribution_from_row 0 1 9 7 0 row_00_01_09_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_07

theorem row_00_01_09_08 : b4RowContribution (![0, 1, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 18] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 18 = 29
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 425 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 18^2 = 425
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_08

theorem weighted_00_01_09_08 : b4RawGapContribution ![0, 1, 9, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 8] = b4GapPatternWeight 1 9 8 * 0 :=
      b4GapContribution_from_row 0 1 9 8 0 row_00_01_09_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_08

theorem row_00_01_09_09 : b4RowContribution (![0, 1, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 19] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 19 = 30
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 462 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 19^2 = 462
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_09

theorem weighted_00_01_09_09 : b4RawGapContribution ![0, 1, 9, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 9] = b4GapPatternWeight 1 9 9 * 0 :=
      b4GapContribution_from_row 0 1 9 9 0 row_00_01_09_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_09

theorem row_00_01_09_10 : b4RowContribution (![0, 1, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 20] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 20 = 31
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 501 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 20^2 = 501
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_10

theorem weighted_00_01_09_10 : b4RawGapContribution ![0, 1, 9, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 10] = b4GapPatternWeight 1 9 10 * 0 :=
      b4GapContribution_from_row 0 1 9 10 0 row_00_01_09_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_10

theorem row_00_01_09_11 : b4RowContribution (![0, 1, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 21] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 21 = 32
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 542 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 21^2 = 542
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_11

theorem weighted_00_01_09_11 : b4RawGapContribution ![0, 1, 9, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 11] = b4GapPatternWeight 1 9 11 * 0 :=
      b4GapContribution_from_row 0 1 9 11 0 row_00_01_09_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_11

theorem row_00_01_09_12 : b4RowContribution (![0, 1, 10, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 22] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 22 = 33
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 585 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 22^2 = 585
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_12

theorem weighted_00_01_09_12 : b4RawGapContribution ![0, 1, 9, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 12] = b4GapPatternWeight 1 9 12 * 0 :=
      b4GapContribution_from_row 0 1 9 12 0 row_00_01_09_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_12

theorem row_00_01_09_13 : b4RowContribution (![0, 1, 10, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 23] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 23 = 34
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 630 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 23^2 = 630
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_13

theorem weighted_00_01_09_13 : b4RawGapContribution ![0, 1, 9, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 13] = b4GapPatternWeight 1 9 13 * 0 :=
      b4GapContribution_from_row 0 1 9 13 0 row_00_01_09_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_13

theorem row_00_01_09_14 : b4RowContribution (![0, 1, 10, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 24] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 24 = 35
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 677 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 24^2 = 677
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_14

theorem weighted_00_01_09_14 : b4RawGapContribution ![0, 1, 9, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 14] = b4GapPatternWeight 1 9 14 * 0 :=
      b4GapContribution_from_row 0 1 9 14 0 row_00_01_09_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_14

theorem row_00_01_09_15 : b4RowContribution (![0, 1, 10, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 25] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 25 = 36
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 726 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 25^2 = 726
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_15

theorem weighted_00_01_09_15 : b4RawGapContribution ![0, 1, 9, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 15] = b4GapPatternWeight 1 9 15 * 0 :=
      b4GapContribution_from_row 0 1 9 15 0 row_00_01_09_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_15

theorem row_00_01_09_16 : b4RowContribution (![0, 1, 10, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 10, 26] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 10 + 26 = 37
    decide
  have hzsq : (∑ i, (((![0, 1, 10, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 777 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 10^2 + 26^2 = 777
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_09_16

theorem weighted_00_01_09_16 : b4RawGapContribution ![0, 1, 9, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 9, 16] = b4GapPatternWeight 1 9 16 * 0 :=
      b4GapContribution_from_row 0 1 9 16 0 row_00_01_09_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_09_16

def dvalues_00_01_09 : Fin 17 → ℕ := ![0, 504, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_01_09

theorem dblock_00_01_09 : b4GapPatternDBlock 0 1 9 = 504 := by
  calc
    b4GapPatternDBlock 0 1 9 = ∑ d : Fin 17, dvalues_00_01_09 d := by
      apply b4GapDBlock_of_rows 0 1 9 dvalues_00_01_09
      intro d
      fin_cases d
      · exact weighted_00_01_09_00
      · exact weighted_00_01_09_01
      · exact weighted_00_01_09_02
      · exact weighted_00_01_09_03
      · exact weighted_00_01_09_04
      · exact weighted_00_01_09_05
      · exact weighted_00_01_09_06
      · exact weighted_00_01_09_07
      · exact weighted_00_01_09_08
      · exact weighted_00_01_09_09
      · exact weighted_00_01_09_10
      · exact weighted_00_01_09_11
      · exact weighted_00_01_09_12
      · exact weighted_00_01_09_13
      · exact weighted_00_01_09_14
      · exact weighted_00_01_09_15
      · exact weighted_00_01_09_16
    _ = 504 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_01_09

end Paper7MomentGapNumeric
