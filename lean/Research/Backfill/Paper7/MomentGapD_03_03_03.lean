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

theorem row_03_03_03_00 : b4RowContribution (![3, 6, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 9, 9] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 9 + 9 = 27
    decide
  have hzsq : (∑ i, (((![3, 6, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 207 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 9^2 + 9^2 = 207
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_03_00

theorem weighted_03_03_03_00 : b4RawGapContribution ![3, 3, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 3, 0] = b4GapPatternWeight 3 3 0 * 0 :=
      b4GapContribution_from_row 3 3 3 0 0 row_03_03_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_03_00

def layers_03_03_03_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 25, 27, 28, 27, 25, 22, 18, 14, 10, 6, 3, 1], ![1, 4, 10, 20, 34, 52, 74, 99, 126, 154, 181, 205, 224, 236, 240, 236, 224, 205, 181]]
#print axioms Paper7MomentGapNumeric.layers_03_03_03_01

theorem cells_03_03_03_01 : QTableValid (![3, 6, 9, 10] : Fin 4 → ℕ) layers_03_03_03_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_03_03_01

theorem valid_03_03_03_01 :
    SparseRowValid (![3, 6, 9, 10] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_03_03_03_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 6, 9, 10] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 3 + 6 + 9 + 10 = 28
      decide
    have hzsq : (∑ i, (((![3, 6, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 226 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 6^2 + 9^2 + 10^2 = 226
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_03_03_01
#print axioms Paper7MomentGapNumeric.valid_03_03_03_01

def qvalues_03_03_03_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_03_03_01

theorem row_03_03_03_01 : b4RowContribution (![3, 6, 9, 10] : Fin 4 → ℕ) = 99 := by
  calc
    b4RowContribution (![3, 6, 9, 10] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_03_03_03_01) :=
      sparseRow_sound (![3, 6, 9, 10] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_03_03_03_01) valid_03_03_03_01
    _ = 99 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_03_03_01 Q := by
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
        _ = 99 := by decide
#print axioms Paper7MomentGapNumeric.row_03_03_03_01

theorem weighted_03_03_03_01 : b4RawGapContribution ![3, 3, 3, 1] = 2376 := by
  calc
    b4RawGapContribution ![3, 3, 3, 1] = b4GapPatternWeight 3 3 1 * 99 :=
      b4GapContribution_from_row 3 3 3 1 99 row_03_03_03_01
    _ = 2376 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_03_01

theorem row_03_03_03_02 : b4RowContribution (![3, 6, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 9, 11] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 9 + 11 = 29
    decide
  have hzsq : (∑ i, (((![3, 6, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 247 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 9^2 + 11^2 = 247
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_03_02

theorem weighted_03_03_03_02 : b4RawGapContribution ![3, 3, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 3, 2] = b4GapPatternWeight 3 3 2 * 0 :=
      b4GapContribution_from_row 3 3 3 2 0 row_03_03_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_03_02

def layers_03_03_03_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 25, 27, 28, 27, 25, 22, 18, 14, 10, 6, 3, 1], ![1, 4, 10, 20, 34, 52, 74, 99, 126, 154, 181, 206, 228, 245, 256, 260, 256, 245, 228]]
#print axioms Paper7MomentGapNumeric.layers_03_03_03_03

theorem cells_03_03_03_03 : QTableValid (![3, 6, 9, 12] : Fin 4 → ℕ) layers_03_03_03_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_03_03_03

theorem valid_03_03_03_03 :
    SparseRowValid (![3, 6, 9, 12] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_03_03_03_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 6, 9, 12] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 3 + 6 + 9 + 12 = 30
      decide
    have hzsq : (∑ i, (((![3, 6, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 6^2 + 9^2 + 12^2 = 270
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_03_03_03
#print axioms Paper7MomentGapNumeric.valid_03_03_03_03

def qvalues_03_03_03_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 74, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_03_03_03

theorem row_03_03_03_03 : b4RowContribution (![3, 6, 9, 12] : Fin 4 → ℕ) = 74 := by
  calc
    b4RowContribution (![3, 6, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_03_03_03_03) :=
      sparseRow_sound (![3, 6, 9, 12] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_03_03_03_03) valid_03_03_03_03
    _ = 74 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_03_03_03 Q := by
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
        _ = 74 := by decide
#print axioms Paper7MomentGapNumeric.row_03_03_03_03

theorem weighted_03_03_03_03 : b4RawGapContribution ![3, 3, 3, 3] = 1776 := by
  calc
    b4RawGapContribution ![3, 3, 3, 3] = b4GapPatternWeight 3 3 3 * 74 :=
      b4GapContribution_from_row 3 3 3 3 74 row_03_03_03_03
    _ = 1776 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_03_03

theorem row_03_03_03_04 : b4RowContribution (![3, 6, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 9, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 9 + 13 = 31
    decide
  have hzsq : (∑ i, (((![3, 6, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 295 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 9^2 + 13^2 = 295
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_03_04

theorem weighted_03_03_03_04 : b4RawGapContribution ![3, 3, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 3, 4] = b4GapPatternWeight 3 3 4 * 0 :=
      b4GapContribution_from_row 3 3 3 4 0 row_03_03_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_03_04

theorem row_03_03_03_05 : b4RowContribution (![3, 6, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 9, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 9 + 14 = 32
    decide
  have hzsq : (∑ i, (((![3, 6, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 322 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 9^2 + 14^2 = 322
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_03_05

theorem weighted_03_03_03_05 : b4RawGapContribution ![3, 3, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 3, 5] = b4GapPatternWeight 3 3 5 * 0 :=
      b4GapContribution_from_row 3 3 3 5 0 row_03_03_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_03_05

theorem row_03_03_03_06 : b4RowContribution (![3, 6, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 9, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 9 + 15 = 33
    decide
  have hzsq : (∑ i, (((![3, 6, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 351 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 9^2 + 15^2 = 351
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_03_06

theorem weighted_03_03_03_06 : b4RawGapContribution ![3, 3, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 3, 6] = b4GapPatternWeight 3 3 6 * 0 :=
      b4GapContribution_from_row 3 3 3 6 0 row_03_03_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_03_06

theorem row_03_03_03_07 : b4RowContribution (![3, 6, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 9, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 9 + 16 = 34
    decide
  have hzsq : (∑ i, (((![3, 6, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 382 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 9^2 + 16^2 = 382
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_03_07

theorem weighted_03_03_03_07 : b4RawGapContribution ![3, 3, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 3, 7] = b4GapPatternWeight 3 3 7 * 0 :=
      b4GapContribution_from_row 3 3 3 7 0 row_03_03_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_03_07

theorem row_03_03_03_08 : b4RowContribution (![3, 6, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 9, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 9 + 17 = 35
    decide
  have hzsq : (∑ i, (((![3, 6, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 415 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 9^2 + 17^2 = 415
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_03_08

theorem weighted_03_03_03_08 : b4RawGapContribution ![3, 3, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 3, 8] = b4GapPatternWeight 3 3 8 * 0 :=
      b4GapContribution_from_row 3 3 3 8 0 row_03_03_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_03_08

theorem row_03_03_03_09 : b4RowContribution (![3, 6, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 9, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 9 + 18 = 36
    decide
  have hzsq : (∑ i, (((![3, 6, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 9^2 + 18^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_03_09

theorem weighted_03_03_03_09 : b4RawGapContribution ![3, 3, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 3, 9] = b4GapPatternWeight 3 3 9 * 0 :=
      b4GapContribution_from_row 3 3 3 9 0 row_03_03_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_03_09

theorem row_03_03_03_10 : b4RowContribution (![3, 6, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 9, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 9 + 19 = 37
    decide
  have hzsq : (∑ i, (((![3, 6, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 487 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 9^2 + 19^2 = 487
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_03_10

theorem weighted_03_03_03_10 : b4RawGapContribution ![3, 3, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 3, 10] = b4GapPatternWeight 3 3 10 * 0 :=
      b4GapContribution_from_row 3 3 3 10 0 row_03_03_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_03_10

def dvalues_03_03_03 : Fin 11 → ℕ := ![0, 2376, 0, 1776, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_03_03

theorem dblock_03_03_03 : b4GapPatternDBlock 3 3 3 = 4152 := by
  calc
    b4GapPatternDBlock 3 3 3 = ∑ d : Fin 11, dvalues_03_03_03 d := by
      apply b4GapDBlock_of_rows 3 3 3 dvalues_03_03_03
      intro d
      fin_cases d
      · exact weighted_03_03_03_00
      · exact weighted_03_03_03_01
      · exact weighted_03_03_03_02
      · exact weighted_03_03_03_03
      · exact weighted_03_03_03_04
      · exact weighted_03_03_03_05
      · exact weighted_03_03_03_06
      · exact weighted_03_03_03_07
      · exact weighted_03_03_03_08
      · exact weighted_03_03_03_09
      · exact weighted_03_03_03_10
    _ = 4152 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_03_03

end Paper7MomentGapNumeric
