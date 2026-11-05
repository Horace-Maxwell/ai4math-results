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

theorem row_00_03_07_00 : b4RowContribution (![0, 3, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 10, 10] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 10 + 10 = 23
    decide
  have hzsq : (∑ i, (((![0, 3, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 209 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 10^2 + 10^2 = 209
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_07_00

theorem weighted_00_03_07_00 : b4RawGapContribution ![0, 3, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 7, 0] = b4GapPatternWeight 3 7 0 * 0 :=
      b4GapContribution_from_row 0 3 7 0 0 row_00_03_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_00

def layers_00_03_07_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 30, 34, 38, 41, 42, 41, 38, 34, 30, 26, 22]]
#print axioms Paper7MomentGapNumeric.layers_00_03_07_01

theorem cells_00_03_07_01 : QTableValid (![0, 3, 10, 11] : Fin 4 → ℕ) layers_00_03_07_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_07_01

theorem valid_00_03_07_01 :
    SparseRowValid (![0, 3, 10, 11] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_00_03_07_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 10, 11] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 10 + 11 = 24
      decide
    have hzsq : (∑ i, (((![0, 3, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 230 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 10^2 + 11^2 = 230
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_07_01
#print axioms Paper7MomentGapNumeric.valid_00_03_07_01

def qvalues_00_03_07_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 41, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_07_01

theorem row_00_03_07_01 : b4RowContribution (![0, 3, 10, 11] : Fin 4 → ℕ) = 59 := by
  calc
    b4RowContribution (![0, 3, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({5, 11} : Finset (Fin 19)) (fun _ => layers_00_03_07_01) :=
      sparseRow_sound (![0, 3, 10, 11] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_00_03_07_01) valid_00_03_07_01
    _ = 59 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_07_01 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 59 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_07_01

theorem weighted_00_03_07_01 : b4RawGapContribution ![0, 3, 7, 1] = 1416 := by
  calc
    b4RawGapContribution ![0, 3, 7, 1] = b4GapPatternWeight 3 7 1 * 59 :=
      b4GapContribution_from_row 0 3 7 1 59 row_00_03_07_01
    _ = 1416 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_01

theorem row_00_03_07_02 : b4RowContribution (![0, 3, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 10, 12] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 10 + 12 = 25
    decide
  have hzsq : (∑ i, (((![0, 3, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 253 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 10^2 + 12^2 = 253
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_07_02

theorem weighted_00_03_07_02 : b4RawGapContribution ![0, 3, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 7, 2] = b4GapPatternWeight 3 7 2 * 0 :=
      b4GapContribution_from_row 0 3 7 2 0 row_00_03_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_02

def layers_00_03_07_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 30, 34, 38, 41, 43, 44, 43, 41, 38, 34, 30]]
#print axioms Paper7MomentGapNumeric.layers_00_03_07_03

theorem cells_00_03_07_03 : QTableValid (![0, 3, 10, 13] : Fin 4 → ℕ) layers_00_03_07_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_07_03

theorem valid_00_03_07_03 :
    SparseRowValid (![0, 3, 10, 13] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_03_07_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 10, 13] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 10 + 13 = 26
      decide
    have hzsq : (∑ i, (((![0, 3, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 278 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 10^2 + 13^2 = 278
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_07_03
#print axioms Paper7MomentGapNumeric.valid_00_03_07_03

def qvalues_00_03_07_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_07_03

theorem row_00_03_07_03 : b4RowContribution (![0, 3, 10, 13] : Fin 4 → ℕ) = 30 := by
  calc
    b4RowContribution (![0, 3, 10, 13] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_00_03_07_03) :=
      sparseRow_sound (![0, 3, 10, 13] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_03_07_03) valid_00_03_07_03
    _ = 30 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_07_03 Q := by
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
        _ = 30 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_07_03

theorem weighted_00_03_07_03 : b4RawGapContribution ![0, 3, 7, 3] = 720 := by
  calc
    b4RawGapContribution ![0, 3, 7, 3] = b4GapPatternWeight 3 7 3 * 30 :=
      b4GapContribution_from_row 0 3 7 3 30 row_00_03_07_03
    _ = 720 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_03

theorem row_00_03_07_04 : b4RowContribution (![0, 3, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 10, 14] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 10 + 14 = 27
    decide
  have hzsq : (∑ i, (((![0, 3, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 305 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 10^2 + 14^2 = 305
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_07_04

theorem weighted_00_03_07_04 : b4RawGapContribution ![0, 3, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 7, 4] = b4GapPatternWeight 3 7 4 * 0 :=
      b4GapContribution_from_row 0 3 7 4 0 row_00_03_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_04

theorem row_00_03_07_05 : b4RowContribution (![0, 3, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 10, 15] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 10 + 15 = 28
    decide
  have hzsq : (∑ i, (((![0, 3, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 334 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 10^2 + 15^2 = 334
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_07_05

theorem weighted_00_03_07_05 : b4RawGapContribution ![0, 3, 7, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 7, 5] = b4GapPatternWeight 3 7 5 * 0 :=
      b4GapContribution_from_row 0 3 7 5 0 row_00_03_07_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_05

theorem row_00_03_07_06 : b4RowContribution (![0, 3, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 10, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 10 + 16 = 29
    decide
  have hzsq : (∑ i, (((![0, 3, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 365 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 10^2 + 16^2 = 365
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_07_06

theorem weighted_00_03_07_06 : b4RawGapContribution ![0, 3, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 7, 6] = b4GapPatternWeight 3 7 6 * 0 :=
      b4GapContribution_from_row 0 3 7 6 0 row_00_03_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_06

theorem row_00_03_07_07 : b4RowContribution (![0, 3, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 10, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 10 + 17 = 30
    decide
  have hzsq : (∑ i, (((![0, 3, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 398 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 10^2 + 17^2 = 398
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_07_07

theorem weighted_00_03_07_07 : b4RawGapContribution ![0, 3, 7, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 7, 7] = b4GapPatternWeight 3 7 7 * 0 :=
      b4GapContribution_from_row 0 3 7 7 0 row_00_03_07_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_07

theorem row_00_03_07_08 : b4RowContribution (![0, 3, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 10, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 10 + 18 = 31
    decide
  have hzsq : (∑ i, (((![0, 3, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 433 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 10^2 + 18^2 = 433
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_07_08

theorem weighted_00_03_07_08 : b4RawGapContribution ![0, 3, 7, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 7, 8] = b4GapPatternWeight 3 7 8 * 0 :=
      b4GapContribution_from_row 0 3 7 8 0 row_00_03_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_08

theorem row_00_03_07_09 : b4RowContribution (![0, 3, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 10, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 10 + 19 = 32
    decide
  have hzsq : (∑ i, (((![0, 3, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 470 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 10^2 + 19^2 = 470
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_07_09

theorem weighted_00_03_07_09 : b4RawGapContribution ![0, 3, 7, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 7, 9] = b4GapPatternWeight 3 7 9 * 0 :=
      b4GapContribution_from_row 0 3 7 9 0 row_00_03_07_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_09

theorem row_00_03_07_10 : b4RowContribution (![0, 3, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 10, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 10 + 20 = 33
    decide
  have hzsq : (∑ i, (((![0, 3, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 509 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 10^2 + 20^2 = 509
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_07_10

theorem weighted_00_03_07_10 : b4RawGapContribution ![0, 3, 7, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 7, 10] = b4GapPatternWeight 3 7 10 * 0 :=
      b4GapContribution_from_row 0 3 7 10 0 row_00_03_07_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_10

theorem row_00_03_07_11 : b4RowContribution (![0, 3, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 10, 21] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 10 + 21 = 34
    decide
  have hzsq : (∑ i, (((![0, 3, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 550 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 10^2 + 21^2 = 550
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_07_11

theorem weighted_00_03_07_11 : b4RawGapContribution ![0, 3, 7, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 7, 11] = b4GapPatternWeight 3 7 11 * 0 :=
      b4GapContribution_from_row 0 3 7 11 0 row_00_03_07_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_11

theorem row_00_03_07_12 : b4RowContribution (![0, 3, 10, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 10, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 10 + 22 = 35
    decide
  have hzsq : (∑ i, (((![0, 3, 10, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 593 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 10^2 + 22^2 = 593
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_07_12

theorem weighted_00_03_07_12 : b4RawGapContribution ![0, 3, 7, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 7, 12] = b4GapPatternWeight 3 7 12 * 0 :=
      b4GapContribution_from_row 0 3 7 12 0 row_00_03_07_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_12

theorem row_00_03_07_13 : b4RowContribution (![0, 3, 10, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 10, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 10 + 23 = 36
    decide
  have hzsq : (∑ i, (((![0, 3, 10, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 638 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 10^2 + 23^2 = 638
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_07_13

theorem weighted_00_03_07_13 : b4RawGapContribution ![0, 3, 7, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 7, 13] = b4GapPatternWeight 3 7 13 * 0 :=
      b4GapContribution_from_row 0 3 7 13 0 row_00_03_07_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_13

theorem row_00_03_07_14 : b4RowContribution (![0, 3, 10, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 10, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 10 + 24 = 37
    decide
  have hzsq : (∑ i, (((![0, 3, 10, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 685 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 10^2 + 24^2 = 685
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_07_14

theorem weighted_00_03_07_14 : b4RawGapContribution ![0, 3, 7, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 7, 14] = b4GapPatternWeight 3 7 14 * 0 :=
      b4GapContribution_from_row 0 3 7 14 0 row_00_03_07_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_07_14

def dvalues_00_03_07 : Fin 15 → ℕ := ![0, 1416, 0, 720, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_03_07

theorem dblock_00_03_07 : b4GapPatternDBlock 0 3 7 = 2136 := by
  calc
    b4GapPatternDBlock 0 3 7 = ∑ d : Fin 15, dvalues_00_03_07 d := by
      apply b4GapDBlock_of_rows 0 3 7 dvalues_00_03_07
      intro d
      fin_cases d
      · exact weighted_00_03_07_00
      · exact weighted_00_03_07_01
      · exact weighted_00_03_07_02
      · exact weighted_00_03_07_03
      · exact weighted_00_03_07_04
      · exact weighted_00_03_07_05
      · exact weighted_00_03_07_06
      · exact weighted_00_03_07_07
      · exact weighted_00_03_07_08
      · exact weighted_00_03_07_09
      · exact weighted_00_03_07_10
      · exact weighted_00_03_07_11
      · exact weighted_00_03_07_12
      · exact weighted_00_03_07_13
      · exact weighted_00_03_07_14
    _ = 2136 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_03_07

end Paper7MomentGapNumeric
