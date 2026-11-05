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

theorem row_03_00_04_00 : b4RowContribution (![3, 3, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 7] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 7 = 20
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 116 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 7^2 = 116
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_00

theorem weighted_03_00_04_00 : b4RawGapContribution ![3, 0, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 0] = b4GapPatternWeight 0 4 0 * 0 :=
      b4GapContribution_from_row 3 0 4 0 0 row_03_00_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_00

theorem row_03_00_04_01 : b4RowContribution (![3, 3, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 8] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 8 = 21
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 131 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 8^2 = 131
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_01

theorem weighted_03_00_04_01 : b4RawGapContribution ![3, 0, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 1] = b4GapPatternWeight 0 4 1 * 0 :=
      b4GapContribution_from_row 3 0 4 1 0 row_03_00_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_01

theorem row_03_00_04_02 : b4RowContribution (![3, 3, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 9] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 9 = 22
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 148 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 9^2 = 148
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_02

theorem weighted_03_00_04_02 : b4RawGapContribution ![3, 0, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 2] = b4GapPatternWeight 0 4 2 * 0 :=
      b4GapContribution_from_row 3 0 4 2 0 row_03_00_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_02

theorem row_03_00_04_03 : b4RowContribution (![3, 3, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 10] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 10 = 23
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 167 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 10^2 = 167
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_03

theorem weighted_03_00_04_03 : b4RawGapContribution ![3, 0, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 3] = b4GapPatternWeight 0 4 3 * 0 :=
      b4GapContribution_from_row 3 0 4 3 0 row_03_00_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_03

theorem row_03_00_04_04 : b4RowContribution (![3, 3, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 11] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 11 = 24
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 188 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 11^2 = 188
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_04

theorem weighted_03_00_04_04 : b4RawGapContribution ![3, 0, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 4] = b4GapPatternWeight 0 4 4 * 0 :=
      b4GapContribution_from_row 3 0 4 4 0 row_03_00_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_04

theorem row_03_00_04_05 : b4RowContribution (![3, 3, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 12] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 12 = 25
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 211 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 12^2 = 211
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_05

theorem weighted_03_00_04_05 : b4RawGapContribution ![3, 0, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 5] = b4GapPatternWeight 0 4 5 * 0 :=
      b4GapContribution_from_row 3 0 4 5 0 row_03_00_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_05

def layers_03_00_04_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 15, 16, 16, 15, 13, 10, 6, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 33, 48, 64, 80, 95, 108, 118, 124, 127, 128, 127, 124, 118, 108, 95]]
#print axioms Paper7MomentGapNumeric.layers_03_00_04_06

theorem cells_03_00_04_06 : QTableValid (![3, 3, 7, 13] : Fin 4 → ℕ) layers_03_00_04_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_00_04_06

theorem valid_03_00_04_06 :
    SparseRowValid (![3, 3, 7, 13] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_00_04_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 3, 7, 13] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 3 + 3 + 7 + 13 = 26
      decide
    have hzsq : (∑ i, (((![3, 3, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 236 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 3^2 + 7^2 + 13^2 = 236
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_00_04_06
#print axioms Paper7MomentGapNumeric.valid_03_00_04_06

def qvalues_03_00_04_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_00_04_06

theorem row_03_00_04_06 : b4RowContribution (![3, 3, 7, 13] : Fin 4 → ℕ) = 48 := by
  calc
    b4RowContribution (![3, 3, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_03_00_04_06) :=
      sparseRow_sound (![3, 3, 7, 13] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_00_04_06) valid_03_00_04_06
    _ = 48 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_00_04_06 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.row_03_00_04_06

theorem weighted_03_00_04_06 : b4RawGapContribution ![3, 0, 4, 6] = 576 := by
  calc
    b4RawGapContribution ![3, 0, 4, 6] = b4GapPatternWeight 0 4 6 * 48 :=
      b4GapContribution_from_row 3 0 4 6 48 row_03_00_04_06
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_06

theorem row_03_00_04_07 : b4RowContribution (![3, 3, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 14] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 14 = 27
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 263 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 14^2 = 263
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_07

theorem weighted_03_00_04_07 : b4RawGapContribution ![3, 0, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 7] = b4GapPatternWeight 0 4 7 * 0 :=
      b4GapContribution_from_row 3 0 4 7 0 row_03_00_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_07

theorem row_03_00_04_08 : b4RowContribution (![3, 3, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 15] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 15 = 28
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 292 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 15^2 = 292
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_08

theorem weighted_03_00_04_08 : b4RawGapContribution ![3, 0, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 8] = b4GapPatternWeight 0 4 8 * 0 :=
      b4GapContribution_from_row 3 0 4 8 0 row_03_00_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_08

theorem row_03_00_04_09 : b4RowContribution (![3, 3, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 16 = 29
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 323 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 16^2 = 323
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_09

theorem weighted_03_00_04_09 : b4RawGapContribution ![3, 0, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 9] = b4GapPatternWeight 0 4 9 * 0 :=
      b4GapContribution_from_row 3 0 4 9 0 row_03_00_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_09

theorem row_03_00_04_10 : b4RowContribution (![3, 3, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 17 = 30
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 356 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 17^2 = 356
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_10

theorem weighted_03_00_04_10 : b4RawGapContribution ![3, 0, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 10] = b4GapPatternWeight 0 4 10 * 0 :=
      b4GapContribution_from_row 3 0 4 10 0 row_03_00_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_10

theorem row_03_00_04_11 : b4RowContribution (![3, 3, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 18 = 31
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 391 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 18^2 = 391
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_11

theorem weighted_03_00_04_11 : b4RawGapContribution ![3, 0, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 11] = b4GapPatternWeight 0 4 11 * 0 :=
      b4GapContribution_from_row 3 0 4 11 0 row_03_00_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_11

theorem row_03_00_04_12 : b4RowContribution (![3, 3, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 19 = 32
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 428 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 19^2 = 428
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_12

theorem weighted_03_00_04_12 : b4RawGapContribution ![3, 0, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 12] = b4GapPatternWeight 0 4 12 * 0 :=
      b4GapContribution_from_row 3 0 4 12 0 row_03_00_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_12

theorem row_03_00_04_13 : b4RowContribution (![3, 3, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 20 = 33
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 467 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 20^2 = 467
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_13

theorem weighted_03_00_04_13 : b4RawGapContribution ![3, 0, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 13] = b4GapPatternWeight 0 4 13 * 0 :=
      b4GapContribution_from_row 3 0 4 13 0 row_03_00_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_13

theorem row_03_00_04_14 : b4RowContribution (![3, 3, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 21] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 21 = 34
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 508 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 21^2 = 508
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_14

theorem weighted_03_00_04_14 : b4RawGapContribution ![3, 0, 4, 14] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 14] = b4GapPatternWeight 0 4 14 * 0 :=
      b4GapContribution_from_row 3 0 4 14 0 row_03_00_04_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_14

theorem row_03_00_04_15 : b4RowContribution (![3, 3, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 22 = 35
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 551 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 22^2 = 551
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_15

theorem weighted_03_00_04_15 : b4RawGapContribution ![3, 0, 4, 15] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 15] = b4GapPatternWeight 0 4 15 * 0 :=
      b4GapContribution_from_row 3 0 4 15 0 row_03_00_04_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_15

theorem row_03_00_04_16 : b4RowContribution (![3, 3, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 23 = 36
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 596 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 23^2 = 596
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_16

theorem weighted_03_00_04_16 : b4RawGapContribution ![3, 0, 4, 16] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 16] = b4GapPatternWeight 0 4 16 * 0 :=
      b4GapContribution_from_row 3 0 4 16 0 row_03_00_04_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_16

theorem row_03_00_04_17 : b4RowContribution (![3, 3, 7, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 7, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 7 + 24 = 37
    decide
  have hzsq : (∑ i, (((![3, 3, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 643 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 7^2 + 24^2 = 643
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_04_17

theorem weighted_03_00_04_17 : b4RawGapContribution ![3, 0, 4, 17] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 4, 17] = b4GapPatternWeight 0 4 17 * 0 :=
      b4GapContribution_from_row 3 0 4 17 0 row_03_00_04_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_04_17

def dvalues_03_00_04 : Fin 18 → ℕ := ![0, 0, 0, 0, 0, 0, 576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_00_04

theorem dblock_03_00_04 : b4GapPatternDBlock 3 0 4 = 576 := by
  calc
    b4GapPatternDBlock 3 0 4 = ∑ d : Fin 18, dvalues_03_00_04 d := by
      apply b4GapDBlock_of_rows 3 0 4 dvalues_03_00_04
      intro d
      fin_cases d
      · exact weighted_03_00_04_00
      · exact weighted_03_00_04_01
      · exact weighted_03_00_04_02
      · exact weighted_03_00_04_03
      · exact weighted_03_00_04_04
      · exact weighted_03_00_04_05
      · exact weighted_03_00_04_06
      · exact weighted_03_00_04_07
      · exact weighted_03_00_04_08
      · exact weighted_03_00_04_09
      · exact weighted_03_00_04_10
      · exact weighted_03_00_04_11
      · exact weighted_03_00_04_12
      · exact weighted_03_00_04_13
      · exact weighted_03_00_04_14
      · exact weighted_03_00_04_15
      · exact weighted_03_00_04_16
      · exact weighted_03_00_04_17
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_00_04

end Paper7MomentGapNumeric
