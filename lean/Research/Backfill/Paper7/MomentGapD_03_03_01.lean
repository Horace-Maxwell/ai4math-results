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

theorem row_03_03_01_00 : b4RowContribution (![3, 6, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 7, 7] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 7 + 7 = 23
    decide
  have hzsq : (∑ i, (((![3, 6, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 143 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 7^2 + 7^2 = 143
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_01_00

theorem weighted_03_03_01_00 : b4RawGapContribution ![3, 3, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 1, 0] = b4GapPatternWeight 3 1 0 * 0 :=
      b4GapContribution_from_row 3 3 1 0 0 row_03_03_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_00

theorem row_03_03_01_01 : b4RowContribution (![3, 6, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 7, 8] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 7 + 8 = 24
    decide
  have hzsq : (∑ i, (((![3, 6, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 158 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 7^2 + 8^2 = 158
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_01_01

theorem weighted_03_03_01_01 : b4RawGapContribution ![3, 3, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 1, 1] = b4GapPatternWeight 3 1 1 * 0 :=
      b4GapContribution_from_row 3 3 1 1 0 row_03_03_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_01

theorem row_03_03_01_02 : b4RowContribution (![3, 6, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 7, 9] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 7 + 9 = 25
    decide
  have hzsq : (∑ i, (((![3, 6, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 175 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 7^2 + 9^2 = 175
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_01_02

theorem weighted_03_03_01_02 : b4RawGapContribution ![3, 3, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 1, 2] = b4GapPatternWeight 3 1 2 * 0 :=
      b4GapContribution_from_row 3 3 1 2 0 row_03_03_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_02

theorem row_03_03_01_03 : b4RowContribution (![3, 6, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 7, 10] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 7 + 10 = 26
    decide
  have hzsq : (∑ i, (((![3, 6, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 194 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 7^2 + 10^2 = 194
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_01_03

theorem weighted_03_03_01_03 : b4RawGapContribution ![3, 3, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 1, 3] = b4GapPatternWeight 3 1 3 * 0 :=
      b4GapContribution_from_row 3 3 1 3 0 row_03_03_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_03

theorem row_03_03_01_04 : b4RowContribution (![3, 6, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 7, 11] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 7 + 11 = 27
    decide
  have hzsq : (∑ i, (((![3, 6, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 215 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 7^2 + 11^2 = 215
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_01_04

theorem weighted_03_03_01_04 : b4RawGapContribution ![3, 3, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 1, 4] = b4GapPatternWeight 3 1 4 * 0 :=
      b4GapContribution_from_row 3 3 1 4 0 row_03_03_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_04

def layers_03_03_01_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 25, 26, 25, 22, 18, 14, 10, 6, 3, 1, 0, 0], ![1, 4, 10, 20, 34, 52, 74, 99, 125, 150, 172, 190, 204, 213, 216, 213, 204, 190, 172]]
#print axioms Paper7MomentGapNumeric.layers_03_03_01_05

theorem cells_03_03_01_05 : QTableValid (![3, 6, 7, 12] : Fin 4 → ℕ) layers_03_03_01_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_03_01_05

theorem valid_03_03_01_05 :
    SparseRowValid (![3, 6, 7, 12] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_03_03_01_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 6, 7, 12] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 3 + 6 + 7 + 12 = 28
      decide
    have hzsq : (∑ i, (((![3, 6, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 238 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 6^2 + 7^2 + 12^2 = 238
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_03_01_05
#print axioms Paper7MomentGapNumeric.valid_03_03_01_05

def qvalues_03_03_01_05 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_03_01_05

theorem row_03_03_01_05 : b4RowContribution (![3, 6, 7, 12] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![3, 6, 7, 12] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_03_03_01_05) :=
      sparseRow_sound (![3, 6, 7, 12] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_03_03_01_05) valid_03_03_01_05
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_03_01_05 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.row_03_03_01_05

theorem weighted_03_03_01_05 : b4RawGapContribution ![3, 3, 1, 5] = 96 := by
  calc
    b4RawGapContribution ![3, 3, 1, 5] = b4GapPatternWeight 3 1 5 * 4 :=
      b4GapContribution_from_row 3 3 1 5 4 row_03_03_01_05
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_05

theorem row_03_03_01_06 : b4RowContribution (![3, 6, 7, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 7, 13] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 7 + 13 = 29
    decide
  have hzsq : (∑ i, (((![3, 6, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 263 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 7^2 + 13^2 = 263
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_01_06

theorem weighted_03_03_01_06 : b4RawGapContribution ![3, 3, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 1, 6] = b4GapPatternWeight 3 1 6 * 0 :=
      b4GapContribution_from_row 3 3 1 6 0 row_03_03_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_06

theorem row_03_03_01_07 : b4RowContribution (![3, 6, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 7, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 7 + 14 = 30
    decide
  have hzsq : (∑ i, (((![3, 6, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 290 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 7^2 + 14^2 = 290
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_01_07

theorem weighted_03_03_01_07 : b4RawGapContribution ![3, 3, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 1, 7] = b4GapPatternWeight 3 1 7 * 0 :=
      b4GapContribution_from_row 3 3 1 7 0 row_03_03_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_07

theorem row_03_03_01_08 : b4RowContribution (![3, 6, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 7, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 7 + 15 = 31
    decide
  have hzsq : (∑ i, (((![3, 6, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 319 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 7^2 + 15^2 = 319
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_01_08

theorem weighted_03_03_01_08 : b4RawGapContribution ![3, 3, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 1, 8] = b4GapPatternWeight 3 1 8 * 0 :=
      b4GapContribution_from_row 3 3 1 8 0 row_03_03_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_08

theorem row_03_03_01_09 : b4RowContribution (![3, 6, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 7, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 7 + 16 = 32
    decide
  have hzsq : (∑ i, (((![3, 6, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 350 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 7^2 + 16^2 = 350
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_01_09

theorem weighted_03_03_01_09 : b4RawGapContribution ![3, 3, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 1, 9] = b4GapPatternWeight 3 1 9 * 0 :=
      b4GapContribution_from_row 3 3 1 9 0 row_03_03_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_09

theorem row_03_03_01_10 : b4RowContribution (![3, 6, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 7, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 7 + 17 = 33
    decide
  have hzsq : (∑ i, (((![3, 6, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 383 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 7^2 + 17^2 = 383
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_01_10

theorem weighted_03_03_01_10 : b4RawGapContribution ![3, 3, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 1, 10] = b4GapPatternWeight 3 1 10 * 0 :=
      b4GapContribution_from_row 3 3 1 10 0 row_03_03_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_10

theorem row_03_03_01_11 : b4RowContribution (![3, 6, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 7, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 7 + 18 = 34
    decide
  have hzsq : (∑ i, (((![3, 6, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 418 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 7^2 + 18^2 = 418
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_01_11

theorem weighted_03_03_01_11 : b4RawGapContribution ![3, 3, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 1, 11] = b4GapPatternWeight 3 1 11 * 0 :=
      b4GapContribution_from_row 3 3 1 11 0 row_03_03_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_11

theorem row_03_03_01_12 : b4RowContribution (![3, 6, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 7, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 7 + 19 = 35
    decide
  have hzsq : (∑ i, (((![3, 6, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 455 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 7^2 + 19^2 = 455
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_01_12

theorem weighted_03_03_01_12 : b4RawGapContribution ![3, 3, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 1, 12] = b4GapPatternWeight 3 1 12 * 0 :=
      b4GapContribution_from_row 3 3 1 12 0 row_03_03_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_12

theorem row_03_03_01_13 : b4RowContribution (![3, 6, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 7, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 7 + 20 = 36
    decide
  have hzsq : (∑ i, (((![3, 6, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 494 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 7^2 + 20^2 = 494
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_01_13

theorem weighted_03_03_01_13 : b4RawGapContribution ![3, 3, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 1, 13] = b4GapPatternWeight 3 1 13 * 0 :=
      b4GapContribution_from_row 3 3 1 13 0 row_03_03_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_13

theorem row_03_03_01_14 : b4RowContribution (![3, 6, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 6, 7, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 6 + 7 + 21 = 37
    decide
  have hzsq : (∑ i, (((![3, 6, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 535 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 6^2 + 7^2 + 21^2 = 535
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_03_01_14

theorem weighted_03_03_01_14 : b4RawGapContribution ![3, 3, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![3, 3, 1, 14] = b4GapPatternWeight 3 1 14 * 0 :=
      b4GapContribution_from_row 3 3 1 14 0 row_03_03_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_03_01_14

def dvalues_03_03_01 : Fin 15 → ℕ := ![0, 0, 0, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_03_01

theorem dblock_03_03_01 : b4GapPatternDBlock 3 3 1 = 96 := by
  calc
    b4GapPatternDBlock 3 3 1 = ∑ d : Fin 15, dvalues_03_03_01 d := by
      apply b4GapDBlock_of_rows 3 3 1 dvalues_03_03_01
      intro d
      fin_cases d
      · exact weighted_03_03_01_00
      · exact weighted_03_03_01_01
      · exact weighted_03_03_01_02
      · exact weighted_03_03_01_03
      · exact weighted_03_03_01_04
      · exact weighted_03_03_01_05
      · exact weighted_03_03_01_06
      · exact weighted_03_03_01_07
      · exact weighted_03_03_01_08
      · exact weighted_03_03_01_09
      · exact weighted_03_03_01_10
      · exact weighted_03_03_01_11
      · exact weighted_03_03_01_12
      · exact weighted_03_03_01_13
      · exact weighted_03_03_01_14
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_03_01

end Paper7MomentGapNumeric
