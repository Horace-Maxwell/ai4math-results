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

theorem row_04_02_01_00 : b4RowContribution (![4, 6, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 7, 7] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 7 + 7 = 24
    decide
  have hzsq : (∑ i, (((![4, 6, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 150 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 7^2 + 7^2 = 150
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_01_00

theorem weighted_04_02_01_00 : b4RawGapContribution ![4, 2, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 1, 0] = b4GapPatternWeight 2 1 0 * 0 :=
      b4GapContribution_from_row 4 2 1 0 0 row_04_02_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_01_00

theorem row_04_02_01_01 : b4RowContribution (![4, 6, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 7, 8] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 7 + 8 = 25
    decide
  have hzsq : (∑ i, (((![4, 6, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 165 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 7^2 + 8^2 = 165
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_01_01

theorem weighted_04_02_01_01 : b4RawGapContribution ![4, 2, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 1, 1] = b4GapPatternWeight 2 1 1 * 0 :=
      b4GapContribution_from_row 4 2 1 1 0 row_04_02_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_01_01

theorem row_04_02_01_02 : b4RowContribution (![4, 6, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 7, 9] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 7 + 9 = 26
    decide
  have hzsq : (∑ i, (((![4, 6, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 182 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 7^2 + 9^2 = 182
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_01_02

theorem weighted_04_02_01_02 : b4RawGapContribution ![4, 2, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 1, 2] = b4GapPatternWeight 2 1 2 * 0 :=
      b4GapContribution_from_row 4 2 1 2 0 row_04_02_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_01_02

theorem row_04_02_01_03 : b4RowContribution (![4, 6, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 7, 10] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 7 + 10 = 27
    decide
  have hzsq : (∑ i, (((![4, 6, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 201 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 7^2 + 10^2 = 201
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_01_03

theorem weighted_04_02_01_03 : b4RawGapContribution ![4, 2, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 1, 3] = b4GapPatternWeight 2 1 3 * 0 :=
      b4GapContribution_from_row 4 2 1 3 0 row_04_02_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_01_03

def layers_04_02_01_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 29, 31, 31, 29, 25, 20, 15, 10, 6, 3, 1, 0], ![1, 4, 10, 20, 35, 55, 80, 109, 140, 171, 200, 225, 244, 256, 260, 256, 244, 225, 200]]
#print axioms Paper7MomentGapNumeric.layers_04_02_01_04

theorem cells_04_02_01_04 : QTableValid (![4, 6, 7, 11] : Fin 4 → ℕ) layers_04_02_01_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_02_01_04

theorem valid_04_02_01_04 :
    SparseRowValid (![4, 6, 7, 11] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_04_02_01_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 6, 7, 11] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 4 + 6 + 7 + 11 = 28
      decide
    have hzsq : (∑ i, (((![4, 6, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 222 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 6^2 + 7^2 + 11^2 = 222
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_02_01_04
#print axioms Paper7MomentGapNumeric.valid_04_02_01_04

def qvalues_04_02_01_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 171, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_02_01_04

theorem row_04_02_01_04 : b4RowContribution (![4, 6, 7, 11] : Fin 4 → ℕ) = 171 := by
  calc
    b4RowContribution (![4, 6, 7, 11] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_04_02_01_04) :=
      sparseRow_sound (![4, 6, 7, 11] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_04_02_01_04) valid_04_02_01_04
    _ = 171 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_02_01_04 Q := by
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
        _ = 171 := by decide
#print axioms Paper7MomentGapNumeric.row_04_02_01_04

theorem weighted_04_02_01_04 : b4RawGapContribution ![4, 2, 1, 4] = 4104 := by
  calc
    b4RawGapContribution ![4, 2, 1, 4] = b4GapPatternWeight 2 1 4 * 171 :=
      b4GapContribution_from_row 4 2 1 4 171 row_04_02_01_04
    _ = 4104 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_01_04

theorem row_04_02_01_05 : b4RowContribution (![4, 6, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 7, 12] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 7 + 12 = 29
    decide
  have hzsq : (∑ i, (((![4, 6, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 245 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 7^2 + 12^2 = 245
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_01_05

theorem weighted_04_02_01_05 : b4RawGapContribution ![4, 2, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 1, 5] = b4GapPatternWeight 2 1 5 * 0 :=
      b4GapContribution_from_row 4 2 1 5 0 row_04_02_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_01_05

def layers_04_02_01_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 29, 31, 31, 29, 25, 20, 15, 10, 6, 3, 1, 0], ![1, 4, 10, 20, 35, 55, 80, 109, 140, 171, 200, 225, 245, 260, 269, 272, 269, 260, 245]]
#print axioms Paper7MomentGapNumeric.layers_04_02_01_06

theorem cells_04_02_01_06 : QTableValid (![4, 6, 7, 13] : Fin 4 → ℕ) layers_04_02_01_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_02_01_06

theorem valid_04_02_01_06 :
    SparseRowValid (![4, 6, 7, 13] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_04_02_01_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 6, 7, 13] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 4 + 6 + 7 + 13 = 30
      decide
    have hzsq : (∑ i, (((![4, 6, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 6^2 + 7^2 + 13^2 = 270
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_02_01_06
#print axioms Paper7MomentGapNumeric.valid_04_02_01_06

def qvalues_04_02_01_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_02_01_06

theorem row_04_02_01_06 : b4RowContribution (![4, 6, 7, 13] : Fin 4 → ℕ) = 80 := by
  calc
    b4RowContribution (![4, 6, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_04_02_01_06) :=
      sparseRow_sound (![4, 6, 7, 13] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_04_02_01_06) valid_04_02_01_06
    _ = 80 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_02_01_06 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 80 := by decide
#print axioms Paper7MomentGapNumeric.row_04_02_01_06

theorem weighted_04_02_01_06 : b4RawGapContribution ![4, 2, 1, 6] = 1920 := by
  calc
    b4RawGapContribution ![4, 2, 1, 6] = b4GapPatternWeight 2 1 6 * 80 :=
      b4GapContribution_from_row 4 2 1 6 80 row_04_02_01_06
    _ = 1920 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_01_06

theorem row_04_02_01_07 : b4RowContribution (![4, 6, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 7, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 7 + 14 = 31
    decide
  have hzsq : (∑ i, (((![4, 6, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 297 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 7^2 + 14^2 = 297
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_01_07

theorem weighted_04_02_01_07 : b4RawGapContribution ![4, 2, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 1, 7] = b4GapPatternWeight 2 1 7 * 0 :=
      b4GapContribution_from_row 4 2 1 7 0 row_04_02_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_01_07

theorem row_04_02_01_08 : b4RowContribution (![4, 6, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 7, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 7 + 15 = 32
    decide
  have hzsq : (∑ i, (((![4, 6, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 326 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 7^2 + 15^2 = 326
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_01_08

theorem weighted_04_02_01_08 : b4RawGapContribution ![4, 2, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 1, 8] = b4GapPatternWeight 2 1 8 * 0 :=
      b4GapContribution_from_row 4 2 1 8 0 row_04_02_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_01_08

theorem row_04_02_01_09 : b4RowContribution (![4, 6, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 7, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 7 + 16 = 33
    decide
  have hzsq : (∑ i, (((![4, 6, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 357 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 7^2 + 16^2 = 357
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_01_09

theorem weighted_04_02_01_09 : b4RawGapContribution ![4, 2, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 1, 9] = b4GapPatternWeight 2 1 9 * 0 :=
      b4GapContribution_from_row 4 2 1 9 0 row_04_02_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_01_09

theorem row_04_02_01_10 : b4RowContribution (![4, 6, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 7, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 7 + 17 = 34
    decide
  have hzsq : (∑ i, (((![4, 6, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 7^2 + 17^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_01_10

theorem weighted_04_02_01_10 : b4RawGapContribution ![4, 2, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 1, 10] = b4GapPatternWeight 2 1 10 * 0 :=
      b4GapContribution_from_row 4 2 1 10 0 row_04_02_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_01_10

theorem row_04_02_01_11 : b4RowContribution (![4, 6, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 7, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 7 + 18 = 35
    decide
  have hzsq : (∑ i, (((![4, 6, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 425 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 7^2 + 18^2 = 425
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_01_11

theorem weighted_04_02_01_11 : b4RawGapContribution ![4, 2, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 1, 11] = b4GapPatternWeight 2 1 11 * 0 :=
      b4GapContribution_from_row 4 2 1 11 0 row_04_02_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_01_11

theorem row_04_02_01_12 : b4RowContribution (![4, 6, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 7, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 7 + 19 = 36
    decide
  have hzsq : (∑ i, (((![4, 6, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 462 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 7^2 + 19^2 = 462
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_01_12

theorem weighted_04_02_01_12 : b4RawGapContribution ![4, 2, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 1, 12] = b4GapPatternWeight 2 1 12 * 0 :=
      b4GapContribution_from_row 4 2 1 12 0 row_04_02_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_01_12

theorem row_04_02_01_13 : b4RowContribution (![4, 6, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 7, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 7 + 20 = 37
    decide
  have hzsq : (∑ i, (((![4, 6, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 501 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 7^2 + 20^2 = 501
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_01_13

theorem weighted_04_02_01_13 : b4RawGapContribution ![4, 2, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 1, 13] = b4GapPatternWeight 2 1 13 * 0 :=
      b4GapContribution_from_row 4 2 1 13 0 row_04_02_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_01_13

def dvalues_04_02_01 : Fin 14 → ℕ := ![0, 0, 0, 0, 4104, 0, 1920, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_02_01

theorem dblock_04_02_01 : b4GapPatternDBlock 4 2 1 = 6024 := by
  calc
    b4GapPatternDBlock 4 2 1 = ∑ d : Fin 14, dvalues_04_02_01 d := by
      apply b4GapDBlock_of_rows 4 2 1 dvalues_04_02_01
      intro d
      fin_cases d
      · exact weighted_04_02_01_00
      · exact weighted_04_02_01_01
      · exact weighted_04_02_01_02
      · exact weighted_04_02_01_03
      · exact weighted_04_02_01_04
      · exact weighted_04_02_01_05
      · exact weighted_04_02_01_06
      · exact weighted_04_02_01_07
      · exact weighted_04_02_01_08
      · exact weighted_04_02_01_09
      · exact weighted_04_02_01_10
      · exact weighted_04_02_01_11
      · exact weighted_04_02_01_12
      · exact weighted_04_02_01_13
    _ = 6024 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_02_01

end Paper7MomentGapNumeric
