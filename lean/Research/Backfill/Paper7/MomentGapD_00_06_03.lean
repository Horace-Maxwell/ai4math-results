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

theorem row_00_06_03_00 : b4RowContribution (![0, 6, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 9, 9] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 9 + 9 = 24
    decide
  have hzsq : (∑ i, (((![0, 6, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 198 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 9^2 + 9^2 = 198
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_03_00

theorem weighted_00_06_03_00 : b4RawGapContribution ![0, 6, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 3, 0] = b4GapPatternWeight 6 3 0 * 0 :=
      b4GapContribution_from_row 0 6 3 0 0 row_00_06_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_03_00

def layers_00_06_03_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 7, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 35, 42, 49, 55, 59, 61, 61, 59, 55, 49, 42, 35]]
#print axioms Paper7MomentGapNumeric.layers_00_06_03_01

theorem cells_00_06_03_01 : QTableValid (![0, 6, 9, 10] : Fin 4 → ℕ) layers_00_06_03_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_06_03_01

theorem valid_00_06_03_01 :
    SparseRowValid (![0, 6, 9, 10] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_00_06_03_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 6, 9, 10] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 6 + 9 + 10 = 25
      decide
    have hzsq : (∑ i, (((![0, 6, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 217 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 6^2 + 9^2 + 10^2 = 217
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_06_03_01
#print axioms Paper7MomentGapNumeric.valid_00_06_03_01

def qvalues_00_06_03_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_06_03_01

theorem row_00_06_03_01 : b4RowContribution (![0, 6, 9, 10] : Fin 4 → ℕ) = 55 := by
  calc
    b4RowContribution (![0, 6, 9, 10] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_00_06_03_01) :=
      sparseRow_sound (![0, 6, 9, 10] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_00_06_03_01) valid_00_06_03_01
    _ = 55 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_06_03_01 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 55 := by decide
#print axioms Paper7MomentGapNumeric.row_00_06_03_01

theorem weighted_00_06_03_01 : b4RawGapContribution ![0, 6, 3, 1] = 1320 := by
  calc
    b4RawGapContribution ![0, 6, 3, 1] = b4GapPatternWeight 6 3 1 * 55 :=
      b4GapContribution_from_row 0 6 3 1 55 row_00_06_03_01
    _ = 1320 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_03_01

def layers_00_06_03_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 7, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 35, 42, 49, 55, 60, 63, 64, 63, 60, 55, 49, 42]]
#print axioms Paper7MomentGapNumeric.layers_00_06_03_02

theorem cells_00_06_03_02 : QTableValid (![0, 6, 9, 11] : Fin 4 → ℕ) layers_00_06_03_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_06_03_02

theorem valid_00_06_03_02 :
    SparseRowValid (![0, 6, 9, 11] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_00_06_03_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 6, 9, 11] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 0 + 6 + 9 + 11 = 26
      decide
    have hzsq : (∑ i, (((![0, 6, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 238 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 6^2 + 9^2 + 11^2 = 238
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_06_03_02
#print axioms Paper7MomentGapNumeric.valid_00_06_03_02

def qvalues_00_06_03_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_06_03_02

theorem row_00_06_03_02 : b4RowContribution (![0, 6, 9, 11] : Fin 4 → ℕ) = 15 := by
  calc
    b4RowContribution (![0, 6, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_00_06_03_02) :=
      sparseRow_sound (![0, 6, 9, 11] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_00_06_03_02) valid_00_06_03_02
    _ = 15 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_06_03_02 Q := by
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
        _ = 15 := by decide
#print axioms Paper7MomentGapNumeric.row_00_06_03_02

theorem weighted_00_06_03_02 : b4RawGapContribution ![0, 6, 3, 2] = 360 := by
  calc
    b4RawGapContribution ![0, 6, 3, 2] = b4GapPatternWeight 6 3 2 * 15 :=
      b4GapContribution_from_row 0 6 3 2 15 row_00_06_03_02
    _ = 360 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_03_02

theorem row_00_06_03_03 : b4RowContribution (![0, 6, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 9, 12] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 9 + 12 = 27
    decide
  have hzsq : (∑ i, (((![0, 6, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 261 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 9^2 + 12^2 = 261
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_03_03

theorem weighted_00_06_03_03 : b4RawGapContribution ![0, 6, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 3, 3] = b4GapPatternWeight 6 3 3 * 0 :=
      b4GapContribution_from_row 0 6 3 3 0 row_00_06_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_03_03

def layers_00_06_03_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 7, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 35, 42, 49, 55, 60, 64, 67, 68, 67, 64, 60, 55]]
#print axioms Paper7MomentGapNumeric.layers_00_06_03_04

theorem cells_00_06_03_04 : QTableValid (![0, 6, 9, 13] : Fin 4 → ℕ) layers_00_06_03_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_06_03_04

theorem valid_00_06_03_04 :
    SparseRowValid (![0, 6, 9, 13] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_06_03_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 6, 9, 13] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 0 + 6 + 9 + 13 = 28
      decide
    have hzsq : (∑ i, (((![0, 6, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 286 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 6^2 + 9^2 + 13^2 = 286
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_06_03_04
#print axioms Paper7MomentGapNumeric.valid_00_06_03_04

def qvalues_00_06_03_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_06_03_04

theorem row_00_06_03_04 : b4RowContribution (![0, 6, 9, 13] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![0, 6, 9, 13] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_00_06_03_04) :=
      sparseRow_sound (![0, 6, 9, 13] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_00_06_03_04) valid_00_06_03_04
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_06_03_04 Q := by
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
        _ = 35 := by decide
#print axioms Paper7MomentGapNumeric.row_00_06_03_04

theorem weighted_00_06_03_04 : b4RawGapContribution ![0, 6, 3, 4] = 840 := by
  calc
    b4RawGapContribution ![0, 6, 3, 4] = b4GapPatternWeight 6 3 4 * 35 :=
      b4GapContribution_from_row 0 6 3 4 35 row_00_06_03_04
    _ = 840 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_03_04

theorem row_00_06_03_05 : b4RowContribution (![0, 6, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 9, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 9 + 14 = 29
    decide
  have hzsq : (∑ i, (((![0, 6, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 313 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 9^2 + 14^2 = 313
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_03_05

theorem weighted_00_06_03_05 : b4RawGapContribution ![0, 6, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 3, 5] = b4GapPatternWeight 6 3 5 * 0 :=
      b4GapContribution_from_row 0 6 3 5 0 row_00_06_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_03_05

theorem row_00_06_03_06 : b4RowContribution (![0, 6, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 9, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 9 + 15 = 30
    decide
  have hzsq : (∑ i, (((![0, 6, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 9^2 + 15^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_03_06

theorem weighted_00_06_03_06 : b4RawGapContribution ![0, 6, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 3, 6] = b4GapPatternWeight 6 3 6 * 0 :=
      b4GapContribution_from_row 0 6 3 6 0 row_00_06_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_03_06

theorem row_00_06_03_07 : b4RowContribution (![0, 6, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 9, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 9 + 16 = 31
    decide
  have hzsq : (∑ i, (((![0, 6, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 373 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 9^2 + 16^2 = 373
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_03_07

theorem weighted_00_06_03_07 : b4RawGapContribution ![0, 6, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 3, 7] = b4GapPatternWeight 6 3 7 * 0 :=
      b4GapContribution_from_row 0 6 3 7 0 row_00_06_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_03_07

theorem row_00_06_03_08 : b4RowContribution (![0, 6, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 9, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 9 + 17 = 32
    decide
  have hzsq : (∑ i, (((![0, 6, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 406 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 9^2 + 17^2 = 406
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_03_08

theorem weighted_00_06_03_08 : b4RawGapContribution ![0, 6, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 3, 8] = b4GapPatternWeight 6 3 8 * 0 :=
      b4GapContribution_from_row 0 6 3 8 0 row_00_06_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_03_08

theorem row_00_06_03_09 : b4RowContribution (![0, 6, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 9, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 9 + 18 = 33
    decide
  have hzsq : (∑ i, (((![0, 6, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 441 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 9^2 + 18^2 = 441
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_03_09

theorem weighted_00_06_03_09 : b4RawGapContribution ![0, 6, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 3, 9] = b4GapPatternWeight 6 3 9 * 0 :=
      b4GapContribution_from_row 0 6 3 9 0 row_00_06_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_03_09

theorem row_00_06_03_10 : b4RowContribution (![0, 6, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 9, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 9 + 19 = 34
    decide
  have hzsq : (∑ i, (((![0, 6, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 478 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 9^2 + 19^2 = 478
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_03_10

theorem weighted_00_06_03_10 : b4RawGapContribution ![0, 6, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 3, 10] = b4GapPatternWeight 6 3 10 * 0 :=
      b4GapContribution_from_row 0 6 3 10 0 row_00_06_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_03_10

theorem row_00_06_03_11 : b4RowContribution (![0, 6, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 9, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 9 + 20 = 35
    decide
  have hzsq : (∑ i, (((![0, 6, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 517 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 9^2 + 20^2 = 517
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_03_11

theorem weighted_00_06_03_11 : b4RawGapContribution ![0, 6, 3, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 3, 11] = b4GapPatternWeight 6 3 11 * 0 :=
      b4GapContribution_from_row 0 6 3 11 0 row_00_06_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_03_11

theorem row_00_06_03_12 : b4RowContribution (![0, 6, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 9, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 9 + 21 = 36
    decide
  have hzsq : (∑ i, (((![0, 6, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 558 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 9^2 + 21^2 = 558
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_03_12

theorem weighted_00_06_03_12 : b4RawGapContribution ![0, 6, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 3, 12] = b4GapPatternWeight 6 3 12 * 0 :=
      b4GapContribution_from_row 0 6 3 12 0 row_00_06_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_03_12

theorem row_00_06_03_13 : b4RowContribution (![0, 6, 9, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 9, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 9 + 22 = 37
    decide
  have hzsq : (∑ i, (((![0, 6, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 601 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 9^2 + 22^2 = 601
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_03_13

theorem weighted_00_06_03_13 : b4RawGapContribution ![0, 6, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 3, 13] = b4GapPatternWeight 6 3 13 * 0 :=
      b4GapContribution_from_row 0 6 3 13 0 row_00_06_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_03_13

def dvalues_00_06_03 : Fin 14 → ℕ := ![0, 1320, 360, 0, 840, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_06_03

theorem dblock_00_06_03 : b4GapPatternDBlock 0 6 3 = 2520 := by
  calc
    b4GapPatternDBlock 0 6 3 = ∑ d : Fin 14, dvalues_00_06_03 d := by
      apply b4GapDBlock_of_rows 0 6 3 dvalues_00_06_03
      intro d
      fin_cases d
      · exact weighted_00_06_03_00
      · exact weighted_00_06_03_01
      · exact weighted_00_06_03_02
      · exact weighted_00_06_03_03
      · exact weighted_00_06_03_04
      · exact weighted_00_06_03_05
      · exact weighted_00_06_03_06
      · exact weighted_00_06_03_07
      · exact weighted_00_06_03_08
      · exact weighted_00_06_03_09
      · exact weighted_00_06_03_10
      · exact weighted_00_06_03_11
      · exact weighted_00_06_03_12
      · exact weighted_00_06_03_13
    _ = 2520 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_06_03

end Paper7MomentGapNumeric
