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

theorem row_01_02_07_00 : b4RowContribution (![1, 3, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 10, 10] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 10 + 10 = 24
    decide
  have hzsq : (∑ i, (((![1, 3, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 210 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 10^2 + 10^2 = 210
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_07_00

theorem weighted_01_02_07_00 : b4RawGapContribution ![1, 2, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 7, 0] = b4GapPatternWeight 2 7 0 * 0 :=
      b4GapContribution_from_row 1 2 7 0 0 row_01_02_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_07_00

def layers_01_02_07_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 8, 8, 8, 8, 8, 8, 7, 5, 3, 1, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 32, 40, 48, 56, 64, 72, 79, 83, 83, 79, 72, 64, 56, 48]]
#print axioms Paper7MomentGapNumeric.layers_01_02_07_01

theorem cells_01_02_07_01 : QTableValid (![1, 3, 10, 11] : Fin 4 → ℕ) layers_01_02_07_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_07_01

theorem valid_01_02_07_01 :
    SparseRowValid (![1, 3, 10, 11] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_02_07_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 10, 11] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 10 + 11 = 25
      decide
    have hzsq : (∑ i, (((![1, 3, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 231 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 10^2 + 11^2 = 231
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_07_01
#print axioms Paper7MomentGapNumeric.valid_01_02_07_01

def qvalues_01_02_07_01 : Fin 19 → ℕ := ![0, 0, 0, 16, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_07_01

theorem row_01_02_07_01 : b4RowContribution (![1, 3, 10, 11] : Fin 4 → ℕ) = 80 := by
  calc
    b4RowContribution (![1, 3, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_02_07_01) :=
      sparseRow_sound (![1, 3, 10, 11] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_02_07_01) valid_01_02_07_01
    _ = 80 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_07_01 Q := by
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
        _ = 80 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_07_01

theorem weighted_01_02_07_01 : b4RawGapContribution ![1, 2, 7, 1] = 1920 := by
  calc
    b4RawGapContribution ![1, 2, 7, 1] = b4GapPatternWeight 2 7 1 * 80 :=
      b4GapContribution_from_row 1 2 7 1 80 row_01_02_07_01
    _ = 1920 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_07_01

theorem row_01_02_07_02 : b4RowContribution (![1, 3, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 10, 12] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 10 + 12 = 26
    decide
  have hzsq : (∑ i, (((![1, 3, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 254 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 10^2 + 12^2 = 254
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_07_02

theorem weighted_01_02_07_02 : b4RawGapContribution ![1, 2, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 7, 2] = b4GapPatternWeight 2 7 2 * 0 :=
      b4GapContribution_from_row 1 2 7 2 0 row_01_02_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_07_02

def layers_01_02_07_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 8, 8, 8, 8, 8, 8, 7, 5, 3, 1, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 32, 40, 48, 56, 64, 72, 79, 84, 87, 87, 84, 79, 72, 64]]
#print axioms Paper7MomentGapNumeric.layers_01_02_07_03

theorem cells_01_02_07_03 : QTableValid (![1, 3, 10, 13] : Fin 4 → ℕ) layers_01_02_07_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_07_03

theorem valid_01_02_07_03 :
    SparseRowValid (![1, 3, 10, 13] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_01_02_07_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 10, 13] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 10 + 13 = 27
      decide
    have hzsq : (∑ i, (((![1, 3, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 279 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 10^2 + 13^2 = 279
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_07_03
#print axioms Paper7MomentGapNumeric.valid_01_02_07_03

def qvalues_01_02_07_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_07_03

theorem row_01_02_07_03 : b4RowContribution (![1, 3, 10, 13] : Fin 4 → ℕ) = 40 := by
  calc
    b4RowContribution (![1, 3, 10, 13] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_01_02_07_03) :=
      sparseRow_sound (![1, 3, 10, 13] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_01_02_07_03) valid_01_02_07_03
    _ = 40 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_07_03 Q := by
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
        _ = 40 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_07_03

theorem weighted_01_02_07_03 : b4RawGapContribution ![1, 2, 7, 3] = 960 := by
  calc
    b4RawGapContribution ![1, 2, 7, 3] = b4GapPatternWeight 2 7 3 * 40 :=
      b4GapContribution_from_row 1 2 7 3 40 row_01_02_07_03
    _ = 960 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_07_03

theorem row_01_02_07_04 : b4RowContribution (![1, 3, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 10, 14] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 10 + 14 = 28
    decide
  have hzsq : (∑ i, (((![1, 3, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 10^2 + 14^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_07_04

theorem weighted_01_02_07_04 : b4RawGapContribution ![1, 2, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 7, 4] = b4GapPatternWeight 2 7 4 * 0 :=
      b4GapContribution_from_row 1 2 7 4 0 row_01_02_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_07_04

theorem row_01_02_07_05 : b4RowContribution (![1, 3, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 10, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 10 + 15 = 29
    decide
  have hzsq : (∑ i, (((![1, 3, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 335 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 10^2 + 15^2 = 335
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_07_05

theorem weighted_01_02_07_05 : b4RawGapContribution ![1, 2, 7, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 7, 5] = b4GapPatternWeight 2 7 5 * 0 :=
      b4GapContribution_from_row 1 2 7 5 0 row_01_02_07_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_07_05

theorem row_01_02_07_06 : b4RowContribution (![1, 3, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 10, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 10 + 16 = 30
    decide
  have hzsq : (∑ i, (((![1, 3, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 366 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 10^2 + 16^2 = 366
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_07_06

theorem weighted_01_02_07_06 : b4RawGapContribution ![1, 2, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 7, 6] = b4GapPatternWeight 2 7 6 * 0 :=
      b4GapContribution_from_row 1 2 7 6 0 row_01_02_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_07_06

theorem row_01_02_07_07 : b4RowContribution (![1, 3, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 10, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 10 + 17 = 31
    decide
  have hzsq : (∑ i, (((![1, 3, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 399 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 10^2 + 17^2 = 399
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_07_07

theorem weighted_01_02_07_07 : b4RawGapContribution ![1, 2, 7, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 7, 7] = b4GapPatternWeight 2 7 7 * 0 :=
      b4GapContribution_from_row 1 2 7 7 0 row_01_02_07_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_07_07

theorem row_01_02_07_08 : b4RowContribution (![1, 3, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 10, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 10 + 18 = 32
    decide
  have hzsq : (∑ i, (((![1, 3, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 434 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 10^2 + 18^2 = 434
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_07_08

theorem weighted_01_02_07_08 : b4RawGapContribution ![1, 2, 7, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 7, 8] = b4GapPatternWeight 2 7 8 * 0 :=
      b4GapContribution_from_row 1 2 7 8 0 row_01_02_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_07_08

theorem row_01_02_07_09 : b4RowContribution (![1, 3, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 10, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 10 + 19 = 33
    decide
  have hzsq : (∑ i, (((![1, 3, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 471 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 10^2 + 19^2 = 471
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_07_09

theorem weighted_01_02_07_09 : b4RawGapContribution ![1, 2, 7, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 7, 9] = b4GapPatternWeight 2 7 9 * 0 :=
      b4GapContribution_from_row 1 2 7 9 0 row_01_02_07_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_07_09

theorem row_01_02_07_10 : b4RowContribution (![1, 3, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 10, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 10 + 20 = 34
    decide
  have hzsq : (∑ i, (((![1, 3, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 510 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 10^2 + 20^2 = 510
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_07_10

theorem weighted_01_02_07_10 : b4RawGapContribution ![1, 2, 7, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 7, 10] = b4GapPatternWeight 2 7 10 * 0 :=
      b4GapContribution_from_row 1 2 7 10 0 row_01_02_07_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_07_10

theorem row_01_02_07_11 : b4RowContribution (![1, 3, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 10, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 10 + 21 = 35
    decide
  have hzsq : (∑ i, (((![1, 3, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 551 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 10^2 + 21^2 = 551
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_07_11

theorem weighted_01_02_07_11 : b4RawGapContribution ![1, 2, 7, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 7, 11] = b4GapPatternWeight 2 7 11 * 0 :=
      b4GapContribution_from_row 1 2 7 11 0 row_01_02_07_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_07_11

theorem row_01_02_07_12 : b4RowContribution (![1, 3, 10, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 10, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 10 + 22 = 36
    decide
  have hzsq : (∑ i, (((![1, 3, 10, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 594 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 10^2 + 22^2 = 594
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_07_12

theorem weighted_01_02_07_12 : b4RawGapContribution ![1, 2, 7, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 7, 12] = b4GapPatternWeight 2 7 12 * 0 :=
      b4GapContribution_from_row 1 2 7 12 0 row_01_02_07_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_07_12

theorem row_01_02_07_13 : b4RowContribution (![1, 3, 10, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 10, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 10 + 23 = 37
    decide
  have hzsq : (∑ i, (((![1, 3, 10, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 639 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 10^2 + 23^2 = 639
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_07_13

theorem weighted_01_02_07_13 : b4RawGapContribution ![1, 2, 7, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 7, 13] = b4GapPatternWeight 2 7 13 * 0 :=
      b4GapContribution_from_row 1 2 7 13 0 row_01_02_07_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_07_13

def dvalues_01_02_07 : Fin 14 → ℕ := ![0, 1920, 0, 960, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_02_07

theorem dblock_01_02_07 : b4GapPatternDBlock 1 2 7 = 2880 := by
  calc
    b4GapPatternDBlock 1 2 7 = ∑ d : Fin 14, dvalues_01_02_07 d := by
      apply b4GapDBlock_of_rows 1 2 7 dvalues_01_02_07
      intro d
      fin_cases d
      · exact weighted_01_02_07_00
      · exact weighted_01_02_07_01
      · exact weighted_01_02_07_02
      · exact weighted_01_02_07_03
      · exact weighted_01_02_07_04
      · exact weighted_01_02_07_05
      · exact weighted_01_02_07_06
      · exact weighted_01_02_07_07
      · exact weighted_01_02_07_08
      · exact weighted_01_02_07_09
      · exact weighted_01_02_07_10
      · exact weighted_01_02_07_11
      · exact weighted_01_02_07_12
      · exact weighted_01_02_07_13
    _ = 2880 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_02_07

end Paper7MomentGapNumeric
