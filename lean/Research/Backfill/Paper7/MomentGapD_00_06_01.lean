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

theorem row_00_06_01_00 : b4RowContribution (![0, 6, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 7] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 7 = 20
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 134 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 7^2 = 134
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_00

theorem weighted_00_06_01_00 : b4RawGapContribution ![0, 6, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 0] = b4GapPatternWeight 6 1 0 * 0 :=
      b4GapContribution_from_row 0 6 1 0 0 row_00_06_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_00

theorem row_00_06_01_01 : b4RowContribution (![0, 6, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 8] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 8 = 21
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 149 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 8^2 = 149
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_01

theorem weighted_00_06_01_01 : b4RawGapContribution ![0, 6, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 1] = b4GapPatternWeight 6 1 1 * 0 :=
      b4GapContribution_from_row 0 6 1 1 0 row_00_06_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_01

theorem row_00_06_01_02 : b4RowContribution (![0, 6, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 9] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 9 = 22
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 166 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 9^2 = 166
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_02

theorem weighted_00_06_01_02 : b4RawGapContribution ![0, 6, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 2] = b4GapPatternWeight 6 1 2 * 0 :=
      b4GapContribution_from_row 0 6 1 2 0 row_00_06_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_02

theorem row_00_06_01_03 : b4RowContribution (![0, 6, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 10] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 10 = 23
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 185 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 10^2 = 185
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_03

theorem weighted_00_06_01_03 : b4RawGapContribution ![0, 6, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 3] = b4GapPatternWeight 6 1 3 * 0 :=
      b4GapContribution_from_row 0 6 1 3 0 row_00_06_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_03

theorem row_00_06_01_04 : b4RowContribution (![0, 6, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 11] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 11 = 24
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 206 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 11^2 = 206
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_04

theorem weighted_00_06_01_04 : b4RawGapContribution ![0, 6, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 4] = b4GapPatternWeight 6 1 4 * 0 :=
      b4GapContribution_from_row 0 6 1 4 0 row_00_06_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_04

def layers_00_06_01_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 35, 41, 46, 50, 53, 55, 55, 53, 50, 46, 41, 35]]
#print axioms Paper7MomentGapNumeric.layers_00_06_01_05

theorem cells_00_06_01_05 : QTableValid (![0, 6, 7, 12] : Fin 4 → ℕ) layers_00_06_01_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_06_01_05

theorem valid_00_06_01_05 :
    SparseRowValid (![0, 6, 7, 12] : Fin 4 → ℕ) ({4, 10} : Finset (Fin 19)) (fun _ => layers_00_06_01_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 6, 7, 12] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 6 + 7 + 12 = 25
      decide
    have hzsq : (∑ i, (((![0, 6, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 229 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 6^2 + 7^2 + 12^2 = 229
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_06_01_05
#print axioms Paper7MomentGapNumeric.valid_00_06_01_05

def qvalues_00_06_01_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 50, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_06_01_05

theorem row_00_06_01_05 : b4RowContribution (![0, 6, 7, 12] : Fin 4 → ℕ) = 65 := by
  calc
    b4RowContribution (![0, 6, 7, 12] : Fin 4 → ℕ) =
        sparseRowValue ({4, 10} : Finset (Fin 19)) (fun _ => layers_00_06_01_05) :=
      sparseRow_sound (![0, 6, 7, 12] : Fin 4 → ℕ) ({4, 10} : Finset (Fin 19)) (fun _ => layers_00_06_01_05) valid_00_06_01_05
    _ = 65 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_06_01_05 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 65 := by decide
#print axioms Paper7MomentGapNumeric.row_00_06_01_05

theorem weighted_00_06_01_05 : b4RawGapContribution ![0, 6, 1, 5] = 1560 := by
  calc
    b4RawGapContribution ![0, 6, 1, 5] = b4GapPatternWeight 6 1 5 * 65 :=
      b4GapContribution_from_row 0 6 1 5 65 row_00_06_01_05
    _ = 1560 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_05

theorem row_00_06_01_06 : b4RowContribution (![0, 6, 7, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 13] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 13 = 26
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 254 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 13^2 = 254
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_06

theorem weighted_00_06_01_06 : b4RawGapContribution ![0, 6, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 6] = b4GapPatternWeight 6 1 6 * 0 :=
      b4GapContribution_from_row 0 6 1 6 0 row_00_06_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_06

def layers_00_06_01_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 35, 41, 46, 50, 53, 55, 56, 56, 55, 53, 50, 46]]
#print axioms Paper7MomentGapNumeric.layers_00_06_01_07

theorem cells_00_06_01_07 : QTableValid (![0, 6, 7, 14] : Fin 4 → ℕ) layers_00_06_01_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_06_01_07

theorem valid_00_06_01_07 :
    SparseRowValid (![0, 6, 7, 14] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_06_01_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 6, 7, 14] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 0 + 6 + 7 + 14 = 27
      decide
    have hzsq : (∑ i, (((![0, 6, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 281 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 6^2 + 7^2 + 14^2 = 281
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_06_01_07
#print axioms Paper7MomentGapNumeric.valid_00_06_01_07

def qvalues_00_06_01_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_06_01_07

theorem row_00_06_01_07 : b4RowContribution (![0, 6, 7, 14] : Fin 4 → ℕ) = 21 := by
  calc
    b4RowContribution (![0, 6, 7, 14] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_00_06_01_07) :=
      sparseRow_sound (![0, 6, 7, 14] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_06_01_07) valid_00_06_01_07
    _ = 21 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_06_01_07 Q := by
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
        _ = 21 := by decide
#print axioms Paper7MomentGapNumeric.row_00_06_01_07

theorem weighted_00_06_01_07 : b4RawGapContribution ![0, 6, 1, 7] = 504 := by
  calc
    b4RawGapContribution ![0, 6, 1, 7] = b4GapPatternWeight 6 1 7 * 21 :=
      b4GapContribution_from_row 0 6 1 7 21 row_00_06_01_07
    _ = 504 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_07

theorem row_00_06_01_08 : b4RowContribution (![0, 6, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 15] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 15 = 28
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 310 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 15^2 = 310
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_08

theorem weighted_00_06_01_08 : b4RawGapContribution ![0, 6, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 8] = b4GapPatternWeight 6 1 8 * 0 :=
      b4GapContribution_from_row 0 6 1 8 0 row_00_06_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_08

theorem row_00_06_01_09 : b4RowContribution (![0, 6, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 16 = 29
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 341 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 16^2 = 341
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_09

theorem weighted_00_06_01_09 : b4RawGapContribution ![0, 6, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 9] = b4GapPatternWeight 6 1 9 * 0 :=
      b4GapContribution_from_row 0 6 1 9 0 row_00_06_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_09

theorem row_00_06_01_10 : b4RowContribution (![0, 6, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 17 = 30
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 374 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 17^2 = 374
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_10

theorem weighted_00_06_01_10 : b4RawGapContribution ![0, 6, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 10] = b4GapPatternWeight 6 1 10 * 0 :=
      b4GapContribution_from_row 0 6 1 10 0 row_00_06_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_10

theorem row_00_06_01_11 : b4RowContribution (![0, 6, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 18 = 31
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 409 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 18^2 = 409
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_11

theorem weighted_00_06_01_11 : b4RawGapContribution ![0, 6, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 11] = b4GapPatternWeight 6 1 11 * 0 :=
      b4GapContribution_from_row 0 6 1 11 0 row_00_06_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_11

theorem row_00_06_01_12 : b4RowContribution (![0, 6, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 19 = 32
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 446 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 19^2 = 446
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_12

theorem weighted_00_06_01_12 : b4RawGapContribution ![0, 6, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 12] = b4GapPatternWeight 6 1 12 * 0 :=
      b4GapContribution_from_row 0 6 1 12 0 row_00_06_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_12

theorem row_00_06_01_13 : b4RowContribution (![0, 6, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 20 = 33
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 485 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 20^2 = 485
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_13

theorem weighted_00_06_01_13 : b4RawGapContribution ![0, 6, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 13] = b4GapPatternWeight 6 1 13 * 0 :=
      b4GapContribution_from_row 0 6 1 13 0 row_00_06_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_13

theorem row_00_06_01_14 : b4RowContribution (![0, 6, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 21] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 21 = 34
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 526 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 21^2 = 526
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_14

theorem weighted_00_06_01_14 : b4RawGapContribution ![0, 6, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 14] = b4GapPatternWeight 6 1 14 * 0 :=
      b4GapContribution_from_row 0 6 1 14 0 row_00_06_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_14

theorem row_00_06_01_15 : b4RowContribution (![0, 6, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 22 = 35
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 569 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 22^2 = 569
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_15

theorem weighted_00_06_01_15 : b4RawGapContribution ![0, 6, 1, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 15] = b4GapPatternWeight 6 1 15 * 0 :=
      b4GapContribution_from_row 0 6 1 15 0 row_00_06_01_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_15

theorem row_00_06_01_16 : b4RowContribution (![0, 6, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 23 = 36
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 614 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 23^2 = 614
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_16

theorem weighted_00_06_01_16 : b4RawGapContribution ![0, 6, 1, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 16] = b4GapPatternWeight 6 1 16 * 0 :=
      b4GapContribution_from_row 0 6 1 16 0 row_00_06_01_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_16

theorem row_00_06_01_17 : b4RowContribution (![0, 6, 7, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 7, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 7 + 24 = 37
    decide
  have hzsq : (∑ i, (((![0, 6, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 661 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 7^2 + 24^2 = 661
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_01_17

theorem weighted_00_06_01_17 : b4RawGapContribution ![0, 6, 1, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 1, 17] = b4GapPatternWeight 6 1 17 * 0 :=
      b4GapContribution_from_row 0 6 1 17 0 row_00_06_01_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_01_17

def dvalues_00_06_01 : Fin 18 → ℕ := ![0, 0, 0, 0, 0, 1560, 0, 504, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_06_01

theorem dblock_00_06_01 : b4GapPatternDBlock 0 6 1 = 2064 := by
  calc
    b4GapPatternDBlock 0 6 1 = ∑ d : Fin 18, dvalues_00_06_01 d := by
      apply b4GapDBlock_of_rows 0 6 1 dvalues_00_06_01
      intro d
      fin_cases d
      · exact weighted_00_06_01_00
      · exact weighted_00_06_01_01
      · exact weighted_00_06_01_02
      · exact weighted_00_06_01_03
      · exact weighted_00_06_01_04
      · exact weighted_00_06_01_05
      · exact weighted_00_06_01_06
      · exact weighted_00_06_01_07
      · exact weighted_00_06_01_08
      · exact weighted_00_06_01_09
      · exact weighted_00_06_01_10
      · exact weighted_00_06_01_11
      · exact weighted_00_06_01_12
      · exact weighted_00_06_01_13
      · exact weighted_00_06_01_14
      · exact weighted_00_06_01_15
      · exact weighted_00_06_01_16
      · exact weighted_00_06_01_17
    _ = 2064 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_06_01

end Paper7MomentGapNumeric
