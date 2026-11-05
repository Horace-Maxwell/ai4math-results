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

theorem row_03_01_03_00 : b4RowContribution (![3, 4, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 7] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 7 = 21
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 123 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 7^2 = 123
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_00

theorem weighted_03_01_03_00 : b4RawGapContribution ![3, 1, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 0] = b4GapPatternWeight 1 3 0 * 0 :=
      b4GapContribution_from_row 3 1 3 0 0 row_03_01_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_00

theorem row_03_01_03_01 : b4RowContribution (![3, 4, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 8] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 8 = 22
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 138 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 8^2 = 138
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_01

theorem weighted_03_01_03_01 : b4RawGapContribution ![3, 1, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 1] = b4GapPatternWeight 1 3 1 * 0 :=
      b4GapContribution_from_row 3 1 3 1 0 row_03_01_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_01

theorem row_03_01_03_02 : b4RowContribution (![3, 4, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 9] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 9 = 23
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 155 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 9^2 = 155
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_02

theorem weighted_03_01_03_02 : b4RawGapContribution ![3, 1, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 2] = b4GapPatternWeight 1 3 2 * 0 :=
      b4GapContribution_from_row 3 1 3 2 0 row_03_01_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_02

theorem row_03_01_03_03 : b4RowContribution (![3, 4, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 10] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 10 = 24
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 174 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 10^2 = 174
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_03

theorem weighted_03_01_03_03 : b4RawGapContribution ![3, 1, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 3] = b4GapPatternWeight 1 3 3 * 0 :=
      b4GapContribution_from_row 3 1 3 3 0 row_03_01_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_03

theorem row_03_01_03_04 : b4RowContribution (![3, 4, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 11] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 11 = 25
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 195 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 11^2 = 195
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_04

theorem weighted_03_01_03_04 : b4RawGapContribution ![3, 1, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 4] = b4GapPatternWeight 1 3 4 * 0 :=
      b4GapContribution_from_row 3 1 3 4 0 row_03_01_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_04

theorem row_03_01_03_05 : b4RowContribution (![3, 4, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 12] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 12 = 26
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 218 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 12^2 = 218
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_05

theorem weighted_03_01_03_05 : b4RawGapContribution ![3, 1, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 5] = b4GapPatternWeight 1 3 5 * 0 :=
      b4GapContribution_from_row 3 1 3 5 0 row_03_01_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_05

theorem row_03_01_03_06 : b4RowContribution (![3, 4, 7, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 13 = 27
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 243 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 13^2 = 243
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_06

theorem weighted_03_01_03_06 : b4RawGapContribution ![3, 1, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 6] = b4GapPatternWeight 1 3 6 * 0 :=
      b4GapContribution_from_row 3 1 3 6 0 row_03_01_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_06

def layers_03_01_03_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 17, 19, 20, 19, 17, 14, 10, 6, 3, 1, 0, 0, 0, 0], ![1, 4, 10, 20, 34, 51, 70, 90, 109, 126, 140, 150, 156, 159, 160, 159, 156, 150, 140]]
#print axioms Paper7MomentGapNumeric.layers_03_01_03_07

theorem cells_03_01_03_07 : QTableValid (![3, 4, 7, 14] : Fin 4 → ℕ) layers_03_01_03_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_01_03_07

theorem valid_03_01_03_07 :
    SparseRowValid (![3, 4, 7, 14] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_03_01_03_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 4, 7, 14] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 3 + 4 + 7 + 14 = 28
      decide
    have hzsq : (∑ i, (((![3, 4, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 4^2 + 7^2 + 14^2 = 270
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_01_03_07
#print axioms Paper7MomentGapNumeric.valid_03_01_03_07

def qvalues_03_01_03_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_01_03_07

theorem row_03_01_03_07 : b4RowContribution (![3, 4, 7, 14] : Fin 4 → ℕ) = 126 := by
  calc
    b4RowContribution (![3, 4, 7, 14] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_03_01_03_07) :=
      sparseRow_sound (![3, 4, 7, 14] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_03_01_03_07) valid_03_01_03_07
    _ = 126 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_01_03_07 Q := by
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
        _ = 126 := by decide
#print axioms Paper7MomentGapNumeric.row_03_01_03_07

theorem weighted_03_01_03_07 : b4RawGapContribution ![3, 1, 3, 7] = 3024 := by
  calc
    b4RawGapContribution ![3, 1, 3, 7] = b4GapPatternWeight 1 3 7 * 126 :=
      b4GapContribution_from_row 3 1 3 7 126 row_03_01_03_07
    _ = 3024 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_07

theorem row_03_01_03_08 : b4RowContribution (![3, 4, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 15 = 29
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 299 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 15^2 = 299
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_08

theorem weighted_03_01_03_08 : b4RawGapContribution ![3, 1, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 8] = b4GapPatternWeight 1 3 8 * 0 :=
      b4GapContribution_from_row 3 1 3 8 0 row_03_01_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_08

theorem row_03_01_03_09 : b4RowContribution (![3, 4, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 16 = 30
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 330 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 16^2 = 330
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_09

theorem weighted_03_01_03_09 : b4RawGapContribution ![3, 1, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 9] = b4GapPatternWeight 1 3 9 * 0 :=
      b4GapContribution_from_row 3 1 3 9 0 row_03_01_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_09

theorem row_03_01_03_10 : b4RowContribution (![3, 4, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 17 = 31
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 363 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 17^2 = 363
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_10

theorem weighted_03_01_03_10 : b4RawGapContribution ![3, 1, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 10] = b4GapPatternWeight 1 3 10 * 0 :=
      b4GapContribution_from_row 3 1 3 10 0 row_03_01_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_10

theorem row_03_01_03_11 : b4RowContribution (![3, 4, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 18 = 32
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 398 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 18^2 = 398
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_11

theorem weighted_03_01_03_11 : b4RawGapContribution ![3, 1, 3, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 11] = b4GapPatternWeight 1 3 11 * 0 :=
      b4GapContribution_from_row 3 1 3 11 0 row_03_01_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_11

theorem row_03_01_03_12 : b4RowContribution (![3, 4, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 19 = 33
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 435 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 19^2 = 435
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_12

theorem weighted_03_01_03_12 : b4RawGapContribution ![3, 1, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 12] = b4GapPatternWeight 1 3 12 * 0 :=
      b4GapContribution_from_row 3 1 3 12 0 row_03_01_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_12

theorem row_03_01_03_13 : b4RowContribution (![3, 4, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 20 = 34
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 474 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 20^2 = 474
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_13

theorem weighted_03_01_03_13 : b4RawGapContribution ![3, 1, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 13] = b4GapPatternWeight 1 3 13 * 0 :=
      b4GapContribution_from_row 3 1 3 13 0 row_03_01_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_13

theorem row_03_01_03_14 : b4RowContribution (![3, 4, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 21 = 35
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 515 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 21^2 = 515
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_14

theorem weighted_03_01_03_14 : b4RawGapContribution ![3, 1, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 14] = b4GapPatternWeight 1 3 14 * 0 :=
      b4GapContribution_from_row 3 1 3 14 0 row_03_01_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_14

theorem row_03_01_03_15 : b4RowContribution (![3, 4, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 22 = 36
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 558 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 22^2 = 558
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_15

theorem weighted_03_01_03_15 : b4RawGapContribution ![3, 1, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 15] = b4GapPatternWeight 1 3 15 * 0 :=
      b4GapContribution_from_row 3 1 3 15 0 row_03_01_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_15

theorem row_03_01_03_16 : b4RowContribution (![3, 4, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 7, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 7 + 23 = 37
    decide
  have hzsq : (∑ i, (((![3, 4, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 603 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 7^2 + 23^2 = 603
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_03_16

theorem weighted_03_01_03_16 : b4RawGapContribution ![3, 1, 3, 16] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 3, 16] = b4GapPatternWeight 1 3 16 * 0 :=
      b4GapContribution_from_row 3 1 3 16 0 row_03_01_03_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_03_16

def dvalues_03_01_03 : Fin 17 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 3024, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_01_03

theorem dblock_03_01_03 : b4GapPatternDBlock 3 1 3 = 3024 := by
  calc
    b4GapPatternDBlock 3 1 3 = ∑ d : Fin 17, dvalues_03_01_03 d := by
      apply b4GapDBlock_of_rows 3 1 3 dvalues_03_01_03
      intro d
      fin_cases d
      · exact weighted_03_01_03_00
      · exact weighted_03_01_03_01
      · exact weighted_03_01_03_02
      · exact weighted_03_01_03_03
      · exact weighted_03_01_03_04
      · exact weighted_03_01_03_05
      · exact weighted_03_01_03_06
      · exact weighted_03_01_03_07
      · exact weighted_03_01_03_08
      · exact weighted_03_01_03_09
      · exact weighted_03_01_03_10
      · exact weighted_03_01_03_11
      · exact weighted_03_01_03_12
      · exact weighted_03_01_03_13
      · exact weighted_03_01_03_14
      · exact weighted_03_01_03_15
      · exact weighted_03_01_03_16
    _ = 3024 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_01_03

end Paper7MomentGapNumeric
