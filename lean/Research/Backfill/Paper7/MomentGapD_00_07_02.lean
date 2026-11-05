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

theorem row_00_07_02_00 : b4RowContribution (![0, 7, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 9, 9] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 9 + 9 = 25
    decide
  have hzsq : (∑ i, (((![0, 7, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 211 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 9^2 + 9^2 = 211
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_02_00

theorem weighted_00_07_02_00 : b4RawGapContribution ![0, 7, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 2, 0] = b4GapPatternWeight 7 2 0 * 0 :=
      b4GapContribution_from_row 0 7 2 0 0 row_00_07_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_02_00

def layers_00_07_02_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 8, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 36, 44, 52, 59, 64, 67, 68, 67, 64, 59, 52, 44]]
#print axioms Paper7MomentGapNumeric.layers_00_07_02_01

theorem cells_00_07_02_01 : QTableValid (![0, 7, 9, 10] : Fin 4 → ℕ) layers_00_07_02_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_07_02_01

theorem valid_00_07_02_01 :
    SparseRowValid (![0, 7, 9, 10] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_07_02_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 7, 9, 10] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 0 + 7 + 9 + 10 = 26
      decide
    have hzsq : (∑ i, (((![0, 7, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 230 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 7^2 + 9^2 + 10^2 = 230
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_07_02_01
#print axioms Paper7MomentGapNumeric.valid_00_07_02_01

def qvalues_00_07_02_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_07_02_01

theorem row_00_07_02_01 : b4RowContribution (![0, 7, 9, 10] : Fin 4 → ℕ) = 44 := by
  calc
    b4RowContribution (![0, 7, 9, 10] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_00_07_02_01) :=
      sparseRow_sound (![0, 7, 9, 10] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_07_02_01) valid_00_07_02_01
    _ = 44 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_07_02_01 Q := by
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
        _ = 44 := by decide
#print axioms Paper7MomentGapNumeric.row_00_07_02_01

theorem weighted_00_07_02_01 : b4RawGapContribution ![0, 7, 2, 1] = 1056 := by
  calc
    b4RawGapContribution ![0, 7, 2, 1] = b4GapPatternWeight 7 2 1 * 44 :=
      b4GapContribution_from_row 0 7 2 1 44 row_00_07_02_01
    _ = 1056 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_02_01

theorem row_00_07_02_02 : b4RowContribution (![0, 7, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 9, 11] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 9 + 11 = 27
    decide
  have hzsq : (∑ i, (((![0, 7, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 251 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 9^2 + 11^2 = 251
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_02_02

theorem weighted_00_07_02_02 : b4RawGapContribution ![0, 7, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 2, 2] = b4GapPatternWeight 7 2 2 * 0 :=
      b4GapContribution_from_row 0 7 2 2 0 row_00_07_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_02_02

def layers_00_07_02_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 8, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 36, 44, 52, 59, 65, 70, 73, 74, 73, 70, 65, 59]]
#print axioms Paper7MomentGapNumeric.layers_00_07_02_03

theorem cells_00_07_02_03 : QTableValid (![0, 7, 9, 12] : Fin 4 → ℕ) layers_00_07_02_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_07_02_03

theorem valid_00_07_02_03 :
    SparseRowValid (![0, 7, 9, 12] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_07_02_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 7, 9, 12] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 0 + 7 + 9 + 12 = 28
      decide
    have hzsq : (∑ i, (((![0, 7, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 274 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 7^2 + 9^2 + 12^2 = 274
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_07_02_03
#print axioms Paper7MomentGapNumeric.valid_00_07_02_03

def qvalues_00_07_02_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_07_02_03

theorem row_00_07_02_03 : b4RowContribution (![0, 7, 9, 12] : Fin 4 → ℕ) = 36 := by
  calc
    b4RowContribution (![0, 7, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_00_07_02_03) :=
      sparseRow_sound (![0, 7, 9, 12] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_07_02_03) valid_00_07_02_03
    _ = 36 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_07_02_03 Q := by
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
        _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.row_00_07_02_03

theorem weighted_00_07_02_03 : b4RawGapContribution ![0, 7, 2, 3] = 864 := by
  calc
    b4RawGapContribution ![0, 7, 2, 3] = b4GapPatternWeight 7 2 3 * 36 :=
      b4GapContribution_from_row 0 7 2 3 36 row_00_07_02_03
    _ = 864 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_02_03

theorem row_00_07_02_04 : b4RowContribution (![0, 7, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 9, 13] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 9 + 13 = 29
    decide
  have hzsq : (∑ i, (((![0, 7, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 299 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 9^2 + 13^2 = 299
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_02_04

theorem weighted_00_07_02_04 : b4RawGapContribution ![0, 7, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 2, 4] = b4GapPatternWeight 7 2 4 * 0 :=
      b4GapContribution_from_row 0 7 2 4 0 row_00_07_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_02_04

theorem row_00_07_02_05 : b4RowContribution (![0, 7, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 9, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 9 + 14 = 30
    decide
  have hzsq : (∑ i, (((![0, 7, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 326 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 9^2 + 14^2 = 326
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_02_05

theorem weighted_00_07_02_05 : b4RawGapContribution ![0, 7, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 2, 5] = b4GapPatternWeight 7 2 5 * 0 :=
      b4GapContribution_from_row 0 7 2 5 0 row_00_07_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_02_05

theorem row_00_07_02_06 : b4RowContribution (![0, 7, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 9, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 9 + 15 = 31
    decide
  have hzsq : (∑ i, (((![0, 7, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 355 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 9^2 + 15^2 = 355
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_02_06

theorem weighted_00_07_02_06 : b4RawGapContribution ![0, 7, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 2, 6] = b4GapPatternWeight 7 2 6 * 0 :=
      b4GapContribution_from_row 0 7 2 6 0 row_00_07_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_02_06

theorem row_00_07_02_07 : b4RowContribution (![0, 7, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 9, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 9 + 16 = 32
    decide
  have hzsq : (∑ i, (((![0, 7, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 386 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 9^2 + 16^2 = 386
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_02_07

theorem weighted_00_07_02_07 : b4RawGapContribution ![0, 7, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 2, 7] = b4GapPatternWeight 7 2 7 * 0 :=
      b4GapContribution_from_row 0 7 2 7 0 row_00_07_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_02_07

theorem row_00_07_02_08 : b4RowContribution (![0, 7, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 9, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 9 + 17 = 33
    decide
  have hzsq : (∑ i, (((![0, 7, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 419 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 9^2 + 17^2 = 419
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_02_08

theorem weighted_00_07_02_08 : b4RawGapContribution ![0, 7, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 2, 8] = b4GapPatternWeight 7 2 8 * 0 :=
      b4GapContribution_from_row 0 7 2 8 0 row_00_07_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_02_08

theorem row_00_07_02_09 : b4RowContribution (![0, 7, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 9, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 9 + 18 = 34
    decide
  have hzsq : (∑ i, (((![0, 7, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 454 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 9^2 + 18^2 = 454
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_02_09

theorem weighted_00_07_02_09 : b4RawGapContribution ![0, 7, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 2, 9] = b4GapPatternWeight 7 2 9 * 0 :=
      b4GapContribution_from_row 0 7 2 9 0 row_00_07_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_02_09

theorem row_00_07_02_10 : b4RowContribution (![0, 7, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 9, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 9 + 19 = 35
    decide
  have hzsq : (∑ i, (((![0, 7, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 491 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 9^2 + 19^2 = 491
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_02_10

theorem weighted_00_07_02_10 : b4RawGapContribution ![0, 7, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 2, 10] = b4GapPatternWeight 7 2 10 * 0 :=
      b4GapContribution_from_row 0 7 2 10 0 row_00_07_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_02_10

theorem row_00_07_02_11 : b4RowContribution (![0, 7, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 9, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 9 + 20 = 36
    decide
  have hzsq : (∑ i, (((![0, 7, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 530 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 9^2 + 20^2 = 530
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_02_11

theorem weighted_00_07_02_11 : b4RawGapContribution ![0, 7, 2, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 2, 11] = b4GapPatternWeight 7 2 11 * 0 :=
      b4GapContribution_from_row 0 7 2 11 0 row_00_07_02_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_02_11

theorem row_00_07_02_12 : b4RowContribution (![0, 7, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 9, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 9 + 21 = 37
    decide
  have hzsq : (∑ i, (((![0, 7, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 571 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 9^2 + 21^2 = 571
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_02_12

theorem weighted_00_07_02_12 : b4RawGapContribution ![0, 7, 2, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 2, 12] = b4GapPatternWeight 7 2 12 * 0 :=
      b4GapContribution_from_row 0 7 2 12 0 row_00_07_02_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_02_12

def dvalues_00_07_02 : Fin 13 → ℕ := ![0, 1056, 0, 864, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_07_02

theorem dblock_00_07_02 : b4GapPatternDBlock 0 7 2 = 1920 := by
  calc
    b4GapPatternDBlock 0 7 2 = ∑ d : Fin 13, dvalues_00_07_02 d := by
      apply b4GapDBlock_of_rows 0 7 2 dvalues_00_07_02
      intro d
      fin_cases d
      · exact weighted_00_07_02_00
      · exact weighted_00_07_02_01
      · exact weighted_00_07_02_02
      · exact weighted_00_07_02_03
      · exact weighted_00_07_02_04
      · exact weighted_00_07_02_05
      · exact weighted_00_07_02_06
      · exact weighted_00_07_02_07
      · exact weighted_00_07_02_08
      · exact weighted_00_07_02_09
      · exact weighted_00_07_02_10
      · exact weighted_00_07_02_11
      · exact weighted_00_07_02_12
    _ = 1920 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_07_02

end Paper7MomentGapNumeric
