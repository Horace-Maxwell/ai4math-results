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

theorem row_02_01_06_00 : b4RowContribution (![2, 3, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 9, 9] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 9 + 9 = 23
    decide
  have hzsq : (∑ i, (((![2, 3, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 175 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 9^2 + 9^2 = 175
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_06_00

theorem weighted_02_01_06_00 : b4RawGapContribution ![2, 1, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 6, 0] = b4GapPatternWeight 1 6 0 * 0 :=
      b4GapContribution_from_row 2 1 6 0 0 row_02_01_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_00

theorem row_02_01_06_01 : b4RowContribution (![2, 3, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 9, 10] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 9 + 10 = 24
    decide
  have hzsq : (∑ i, (((![2, 3, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 194 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 9^2 + 10^2 = 194
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_06_01

theorem weighted_02_01_06_01 : b4RawGapContribution ![2, 1, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 6, 1] = b4GapPatternWeight 1 6 1 * 0 :=
      b4GapContribution_from_row 2 1 6 1 0 row_02_01_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_01

def layers_02_01_06_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 11, 12, 12, 12, 12, 12, 11, 9, 6, 3, 1, 0, 0, 0, 0], ![1, 4, 10, 19, 30, 42, 54, 66, 78, 90, 101, 110, 115, 115, 110, 101, 90, 78, 66]]
#print axioms Paper7MomentGapNumeric.layers_02_01_06_02

theorem cells_02_01_06_02 : QTableValid (![2, 3, 9, 11] : Fin 4 → ℕ) layers_02_01_06_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_06_02

theorem valid_02_01_06_02 :
    SparseRowValid (![2, 3, 9, 11] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_02_01_06_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 9, 11] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 9 + 11 = 25
      decide
    have hzsq : (∑ i, (((![2, 3, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 215 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 9^2 + 11^2 = 215
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_06_02
#print axioms Paper7MomentGapNumeric.valid_02_01_06_02

def qvalues_02_01_06_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_06_02

theorem row_02_01_06_02 : b4RowContribution (![2, 3, 9, 11] : Fin 4 → ℕ) = 110 := by
  calc
    b4RowContribution (![2, 3, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({11} : Finset (Fin 19)) (fun _ => layers_02_01_06_02) :=
      sparseRow_sound (![2, 3, 9, 11] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_02_01_06_02) valid_02_01_06_02
    _ = 110 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_06_02 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 110 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_06_02

theorem weighted_02_01_06_02 : b4RawGapContribution ![2, 1, 6, 2] = 2640 := by
  calc
    b4RawGapContribution ![2, 1, 6, 2] = b4GapPatternWeight 1 6 2 * 110 :=
      b4GapContribution_from_row 2 1 6 2 110 row_02_01_06_02
    _ = 2640 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_02

def layers_02_01_06_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 11, 12, 12, 12, 12, 12, 11, 9, 6, 3, 1, 0, 0, 0, 0], ![1, 4, 10, 19, 30, 42, 54, 66, 78, 90, 101, 110, 116, 118, 116, 110, 101, 90, 78]]
#print axioms Paper7MomentGapNumeric.layers_02_01_06_03

theorem cells_02_01_06_03 : QTableValid (![2, 3, 9, 12] : Fin 4 → ℕ) layers_02_01_06_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_06_03

theorem valid_02_01_06_03 :
    SparseRowValid (![2, 3, 9, 12] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_01_06_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 9, 12] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 9 + 12 = 26
      decide
    have hzsq : (∑ i, (((![2, 3, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 238 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 9^2 + 12^2 = 238
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_06_03
#print axioms Paper7MomentGapNumeric.valid_02_01_06_03

def qvalues_02_01_06_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_06_03

theorem row_02_01_06_03 : b4RowContribution (![2, 3, 9, 12] : Fin 4 → ℕ) = 30 := by
  calc
    b4RowContribution (![2, 3, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_02_01_06_03) :=
      sparseRow_sound (![2, 3, 9, 12] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_01_06_03) valid_02_01_06_03
    _ = 30 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_06_03 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 30 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_06_03

theorem weighted_02_01_06_03 : b4RawGapContribution ![2, 1, 6, 3] = 720 := by
  calc
    b4RawGapContribution ![2, 1, 6, 3] = b4GapPatternWeight 1 6 3 * 30 :=
      b4GapContribution_from_row 2 1 6 3 30 row_02_01_06_03
    _ = 720 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_03

theorem row_02_01_06_04 : b4RowContribution (![2, 3, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 9, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 9 + 13 = 27
    decide
  have hzsq : (∑ i, (((![2, 3, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 263 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 9^2 + 13^2 = 263
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_06_04

theorem weighted_02_01_06_04 : b4RawGapContribution ![2, 1, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 6, 4] = b4GapPatternWeight 1 6 4 * 0 :=
      b4GapContribution_from_row 2 1 6 4 0 row_02_01_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_04

theorem row_02_01_06_05 : b4RowContribution (![2, 3, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 9, 14] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 9 + 14 = 28
    decide
  have hzsq : (∑ i, (((![2, 3, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 290 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 9^2 + 14^2 = 290
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_06_05

theorem weighted_02_01_06_05 : b4RawGapContribution ![2, 1, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 6, 5] = b4GapPatternWeight 1 6 5 * 0 :=
      b4GapContribution_from_row 2 1 6 5 0 row_02_01_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_05

theorem row_02_01_06_06 : b4RowContribution (![2, 3, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 9, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 9 + 15 = 29
    decide
  have hzsq : (∑ i, (((![2, 3, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 319 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 9^2 + 15^2 = 319
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_06_06

theorem weighted_02_01_06_06 : b4RawGapContribution ![2, 1, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 6, 6] = b4GapPatternWeight 1 6 6 * 0 :=
      b4GapContribution_from_row 2 1 6 6 0 row_02_01_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_06

theorem row_02_01_06_07 : b4RowContribution (![2, 3, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 9, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 9 + 16 = 30
    decide
  have hzsq : (∑ i, (((![2, 3, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 350 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 9^2 + 16^2 = 350
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_06_07

theorem weighted_02_01_06_07 : b4RawGapContribution ![2, 1, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 6, 7] = b4GapPatternWeight 1 6 7 * 0 :=
      b4GapContribution_from_row 2 1 6 7 0 row_02_01_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_07

theorem row_02_01_06_08 : b4RowContribution (![2, 3, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 9, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 9 + 17 = 31
    decide
  have hzsq : (∑ i, (((![2, 3, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 383 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 9^2 + 17^2 = 383
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_06_08

theorem weighted_02_01_06_08 : b4RawGapContribution ![2, 1, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 6, 8] = b4GapPatternWeight 1 6 8 * 0 :=
      b4GapContribution_from_row 2 1 6 8 0 row_02_01_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_08

theorem row_02_01_06_09 : b4RowContribution (![2, 3, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 9, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 9 + 18 = 32
    decide
  have hzsq : (∑ i, (((![2, 3, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 418 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 9^2 + 18^2 = 418
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_06_09

theorem weighted_02_01_06_09 : b4RawGapContribution ![2, 1, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 6, 9] = b4GapPatternWeight 1 6 9 * 0 :=
      b4GapContribution_from_row 2 1 6 9 0 row_02_01_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_09

theorem row_02_01_06_10 : b4RowContribution (![2, 3, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 9, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 9 + 19 = 33
    decide
  have hzsq : (∑ i, (((![2, 3, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 455 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 9^2 + 19^2 = 455
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_06_10

theorem weighted_02_01_06_10 : b4RawGapContribution ![2, 1, 6, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 6, 10] = b4GapPatternWeight 1 6 10 * 0 :=
      b4GapContribution_from_row 2 1 6 10 0 row_02_01_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_10

theorem row_02_01_06_11 : b4RowContribution (![2, 3, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 9, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 9 + 20 = 34
    decide
  have hzsq : (∑ i, (((![2, 3, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 494 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 9^2 + 20^2 = 494
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_06_11

theorem weighted_02_01_06_11 : b4RawGapContribution ![2, 1, 6, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 6, 11] = b4GapPatternWeight 1 6 11 * 0 :=
      b4GapContribution_from_row 2 1 6 11 0 row_02_01_06_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_11

theorem row_02_01_06_12 : b4RowContribution (![2, 3, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 9, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 9 + 21 = 35
    decide
  have hzsq : (∑ i, (((![2, 3, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 535 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 9^2 + 21^2 = 535
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_06_12

theorem weighted_02_01_06_12 : b4RawGapContribution ![2, 1, 6, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 6, 12] = b4GapPatternWeight 1 6 12 * 0 :=
      b4GapContribution_from_row 2 1 6 12 0 row_02_01_06_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_12

theorem row_02_01_06_13 : b4RowContribution (![2, 3, 9, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 9, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 9 + 22 = 36
    decide
  have hzsq : (∑ i, (((![2, 3, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 578 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 9^2 + 22^2 = 578
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_06_13

theorem weighted_02_01_06_13 : b4RawGapContribution ![2, 1, 6, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 6, 13] = b4GapPatternWeight 1 6 13 * 0 :=
      b4GapContribution_from_row 2 1 6 13 0 row_02_01_06_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_13

theorem row_02_01_06_14 : b4RowContribution (![2, 3, 9, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 9, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 9 + 23 = 37
    decide
  have hzsq : (∑ i, (((![2, 3, 9, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 623 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 9^2 + 23^2 = 623
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_06_14

theorem weighted_02_01_06_14 : b4RawGapContribution ![2, 1, 6, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 6, 14] = b4GapPatternWeight 1 6 14 * 0 :=
      b4GapContribution_from_row 2 1 6 14 0 row_02_01_06_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_06_14

def dvalues_02_01_06 : Fin 15 → ℕ := ![0, 0, 2640, 720, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_01_06

theorem dblock_02_01_06 : b4GapPatternDBlock 2 1 6 = 3360 := by
  calc
    b4GapPatternDBlock 2 1 6 = ∑ d : Fin 15, dvalues_02_01_06 d := by
      apply b4GapDBlock_of_rows 2 1 6 dvalues_02_01_06
      intro d
      fin_cases d
      · exact weighted_02_01_06_00
      · exact weighted_02_01_06_01
      · exact weighted_02_01_06_02
      · exact weighted_02_01_06_03
      · exact weighted_02_01_06_04
      · exact weighted_02_01_06_05
      · exact weighted_02_01_06_06
      · exact weighted_02_01_06_07
      · exact weighted_02_01_06_08
      · exact weighted_02_01_06_09
      · exact weighted_02_01_06_10
      · exact weighted_02_01_06_11
      · exact weighted_02_01_06_12
      · exact weighted_02_01_06_13
      · exact weighted_02_01_06_14
    _ = 3360 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_01_06

end Paper7MomentGapNumeric
