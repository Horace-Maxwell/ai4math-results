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

theorem row_02_05_02_00 : b4RowContribution (![2, 7, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 9, 9] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 9 + 9 = 27
    decide
  have hzsq : (∑ i, (((![2, 7, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 215 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 9^2 + 9^2 = 215
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_02_00

theorem weighted_02_05_02_00 : b4RawGapContribution ![2, 5, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 2, 0] = b4GapPatternWeight 5 2 0 * 0 :=
      b4GapContribution_from_row 2 5 2 0 0 row_02_05_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_02_00

def layers_02_05_02_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 23, 24, 23, 21, 18, 15, 12, 9, 6, 3, 1], ![1, 4, 10, 19, 31, 46, 64, 85, 108, 132, 155, 175, 190, 199, 202, 199, 190, 175, 155]]
#print axioms Paper7MomentGapNumeric.layers_02_05_02_01

theorem cells_02_05_02_01 : QTableValid (![2, 7, 9, 10] : Fin 4 → ℕ) layers_02_05_02_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_05_02_01

theorem valid_02_05_02_01 :
    SparseRowValid (![2, 7, 9, 10] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_02_05_02_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 7, 9, 10] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 2 + 7 + 9 + 10 = 28
      decide
    have hzsq : (∑ i, (((![2, 7, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 234 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 7^2 + 9^2 + 10^2 = 234
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_05_02_01
#print axioms Paper7MomentGapNumeric.valid_02_05_02_01

def qvalues_02_05_02_01 : Fin 19 → ℕ := ![0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_05_02_01

theorem row_02_05_02_01 : b4RowContribution (![2, 7, 9, 10] : Fin 4 → ℕ) = 19 := by
  calc
    b4RowContribution (![2, 7, 9, 10] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_02_05_02_01) :=
      sparseRow_sound (![2, 7, 9, 10] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_02_05_02_01) valid_02_05_02_01
    _ = 19 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_05_02_01 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 19 := by decide
#print axioms Paper7MomentGapNumeric.row_02_05_02_01

theorem weighted_02_05_02_01 : b4RawGapContribution ![2, 5, 2, 1] = 456 := by
  calc
    b4RawGapContribution ![2, 5, 2, 1] = b4GapPatternWeight 5 2 1 * 19 :=
      b4GapContribution_from_row 2 5 2 1 19 row_02_05_02_01
    _ = 456 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_02_01

theorem row_02_05_02_02 : b4RowContribution (![2, 7, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 9, 11] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 9 + 11 = 29
    decide
  have hzsq : (∑ i, (((![2, 7, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 255 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 9^2 + 11^2 = 255
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_02_02

theorem weighted_02_05_02_02 : b4RawGapContribution ![2, 5, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 2, 2] = b4GapPatternWeight 5 2 2 * 0 :=
      b4GapContribution_from_row 2 5 2 2 0 row_02_05_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_02_02

def layers_02_05_02_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 23, 24, 23, 21, 18, 15, 12, 9, 6, 3, 1], ![1, 4, 10, 19, 31, 46, 64, 85, 108, 132, 155, 176, 194, 208, 217, 220, 217, 208, 194]]
#print axioms Paper7MomentGapNumeric.layers_02_05_02_03

theorem cells_02_05_02_03 : QTableValid (![2, 7, 9, 12] : Fin 4 → ℕ) layers_02_05_02_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_05_02_03

theorem valid_02_05_02_03 :
    SparseRowValid (![2, 7, 9, 12] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_02_05_02_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 7, 9, 12] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 2 + 7 + 9 + 12 = 30
      decide
    have hzsq : (∑ i, (((![2, 7, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 278 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 7^2 + 9^2 + 12^2 = 278
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_05_02_03
#print axioms Paper7MomentGapNumeric.valid_02_05_02_03

def qvalues_02_05_02_03 : Fin 19 → ℕ := ![0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_05_02_03

theorem row_02_05_02_03 : b4RowContribution (![2, 7, 9, 12] : Fin 4 → ℕ) = 10 := by
  calc
    b4RowContribution (![2, 7, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({2} : Finset (Fin 19)) (fun _ => layers_02_05_02_03) :=
      sparseRow_sound (![2, 7, 9, 12] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_02_05_02_03) valid_02_05_02_03
    _ = 10 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_05_02_03 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 10 := by decide
#print axioms Paper7MomentGapNumeric.row_02_05_02_03

theorem weighted_02_05_02_03 : b4RawGapContribution ![2, 5, 2, 3] = 240 := by
  calc
    b4RawGapContribution ![2, 5, 2, 3] = b4GapPatternWeight 5 2 3 * 10 :=
      b4GapContribution_from_row 2 5 2 3 10 row_02_05_02_03
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_02_03

theorem row_02_05_02_04 : b4RowContribution (![2, 7, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 9, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 9 + 13 = 31
    decide
  have hzsq : (∑ i, (((![2, 7, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 303 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 9^2 + 13^2 = 303
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_02_04

theorem weighted_02_05_02_04 : b4RawGapContribution ![2, 5, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 2, 4] = b4GapPatternWeight 5 2 4 * 0 :=
      b4GapContribution_from_row 2 5 2 4 0 row_02_05_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_02_04

theorem row_02_05_02_05 : b4RowContribution (![2, 7, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 9, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 9 + 14 = 32
    decide
  have hzsq : (∑ i, (((![2, 7, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 330 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 9^2 + 14^2 = 330
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_02_05

theorem weighted_02_05_02_05 : b4RawGapContribution ![2, 5, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 2, 5] = b4GapPatternWeight 5 2 5 * 0 :=
      b4GapContribution_from_row 2 5 2 5 0 row_02_05_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_02_05

theorem row_02_05_02_06 : b4RowContribution (![2, 7, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 9, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 9 + 15 = 33
    decide
  have hzsq : (∑ i, (((![2, 7, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 359 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 9^2 + 15^2 = 359
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_02_06

theorem weighted_02_05_02_06 : b4RawGapContribution ![2, 5, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 2, 6] = b4GapPatternWeight 5 2 6 * 0 :=
      b4GapContribution_from_row 2 5 2 6 0 row_02_05_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_02_06

theorem row_02_05_02_07 : b4RowContribution (![2, 7, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 9, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 9 + 16 = 34
    decide
  have hzsq : (∑ i, (((![2, 7, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 9^2 + 16^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_02_07

theorem weighted_02_05_02_07 : b4RawGapContribution ![2, 5, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 2, 7] = b4GapPatternWeight 5 2 7 * 0 :=
      b4GapContribution_from_row 2 5 2 7 0 row_02_05_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_02_07

theorem row_02_05_02_08 : b4RowContribution (![2, 7, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 9, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 9 + 17 = 35
    decide
  have hzsq : (∑ i, (((![2, 7, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 423 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 9^2 + 17^2 = 423
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_02_08

theorem weighted_02_05_02_08 : b4RawGapContribution ![2, 5, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 2, 8] = b4GapPatternWeight 5 2 8 * 0 :=
      b4GapContribution_from_row 2 5 2 8 0 row_02_05_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_02_08

theorem row_02_05_02_09 : b4RowContribution (![2, 7, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 9, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 9 + 18 = 36
    decide
  have hzsq : (∑ i, (((![2, 7, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 458 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 9^2 + 18^2 = 458
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_02_09

theorem weighted_02_05_02_09 : b4RawGapContribution ![2, 5, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 2, 9] = b4GapPatternWeight 5 2 9 * 0 :=
      b4GapContribution_from_row 2 5 2 9 0 row_02_05_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_02_09

theorem row_02_05_02_10 : b4RowContribution (![2, 7, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 9, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 9 + 19 = 37
    decide
  have hzsq : (∑ i, (((![2, 7, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 495 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 9^2 + 19^2 = 495
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_02_10

theorem weighted_02_05_02_10 : b4RawGapContribution ![2, 5, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 2, 10] = b4GapPatternWeight 5 2 10 * 0 :=
      b4GapContribution_from_row 2 5 2 10 0 row_02_05_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_02_10

def dvalues_02_05_02 : Fin 11 → ℕ := ![0, 456, 0, 240, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_05_02

theorem dblock_02_05_02 : b4GapPatternDBlock 2 5 2 = 696 := by
  calc
    b4GapPatternDBlock 2 5 2 = ∑ d : Fin 11, dvalues_02_05_02 d := by
      apply b4GapDBlock_of_rows 2 5 2 dvalues_02_05_02
      intro d
      fin_cases d
      · exact weighted_02_05_02_00
      · exact weighted_02_05_02_01
      · exact weighted_02_05_02_02
      · exact weighted_02_05_02_03
      · exact weighted_02_05_02_04
      · exact weighted_02_05_02_05
      · exact weighted_02_05_02_06
      · exact weighted_02_05_02_07
      · exact weighted_02_05_02_08
      · exact weighted_02_05_02_09
      · exact weighted_02_05_02_10
    _ = 696 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_05_02

end Paper7MomentGapNumeric
