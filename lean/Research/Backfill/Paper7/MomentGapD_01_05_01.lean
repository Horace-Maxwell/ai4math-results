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

theorem row_01_05_01_00 : b4RowContribution (![1, 6, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 7] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 7 = 21
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 135 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 7^2 = 135
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_00

theorem weighted_01_05_01_00 : b4RawGapContribution ![1, 5, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 0] = b4GapPatternWeight 5 1 0 * 0 :=
      b4GapContribution_from_row 1 5 1 0 0 row_01_05_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_00

theorem row_01_05_01_01 : b4RowContribution (![1, 6, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 8] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 8 = 22
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 150 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 8^2 = 150
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_01

theorem weighted_01_05_01_01 : b4RawGapContribution ![1, 5, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 1] = b4GapPatternWeight 5 1 1 * 0 :=
      b4GapContribution_from_row 1 5 1 1 0 row_01_05_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_01

theorem row_01_05_01_02 : b4RowContribution (![1, 6, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 9] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 9 = 23
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 167 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 9^2 = 167
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_02

theorem weighted_01_05_01_02 : b4RawGapContribution ![1, 5, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 2] = b4GapPatternWeight 5 1 2 * 0 :=
      b4GapContribution_from_row 1 5 1 2 0 row_01_05_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_02

theorem row_01_05_01_03 : b4RowContribution (![1, 6, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 10] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 10 = 24
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 186 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 10^2 = 186
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_03

theorem weighted_01_05_01_03 : b4RawGapContribution ![1, 5, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 3] = b4GapPatternWeight 5 1 3 * 0 :=
      b4GapContribution_from_row 1 5 1 3 0 row_01_05_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_03

theorem row_01_05_01_04 : b4RowContribution (![1, 6, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 11] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 11 = 25
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 207 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 11^2 = 207
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_04

theorem weighted_01_05_01_04 : b4RawGapContribution ![1, 5, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 4] = b4GapPatternWeight 5 1 4 * 0 :=
      b4GapContribution_from_row 1 5 1 4 0 row_01_05_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_04

def layers_01_05_01_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 14, 13, 11, 9, 7, 5, 3, 1, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 36, 49, 63, 76, 87, 96, 103, 108, 110, 108, 103, 96, 87, 76]]
#print axioms Paper7MomentGapNumeric.layers_01_05_01_05

theorem cells_01_05_01_05 : QTableValid (![1, 6, 7, 12] : Fin 4 → ℕ) layers_01_05_01_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_05_01_05

theorem valid_01_05_01_05 :
    SparseRowValid (![1, 6, 7, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_01_05_01_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 6, 7, 12] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 1 + 6 + 7 + 12 = 26
      decide
    have hzsq : (∑ i, (((![1, 6, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 230 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 6^2 + 7^2 + 12^2 = 230
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_05_01_05
#print axioms Paper7MomentGapNumeric.valid_01_05_01_05

def qvalues_01_05_01_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_05_01_05

theorem row_01_05_01_05 : b4RowContribution (![1, 6, 7, 12] : Fin 4 → ℕ) = 76 := by
  calc
    b4RowContribution (![1, 6, 7, 12] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_01_05_01_05) :=
      sparseRow_sound (![1, 6, 7, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_01_05_01_05) valid_01_05_01_05
    _ = 76 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_05_01_05 Q := by
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
        _ = 76 := by decide
#print axioms Paper7MomentGapNumeric.row_01_05_01_05

theorem weighted_01_05_01_05 : b4RawGapContribution ![1, 5, 1, 5] = 1824 := by
  calc
    b4RawGapContribution ![1, 5, 1, 5] = b4GapPatternWeight 5 1 5 * 76 :=
      b4GapContribution_from_row 1 5 1 5 76 row_01_05_01_05
    _ = 1824 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_05

theorem row_01_05_01_06 : b4RowContribution (![1, 6, 7, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 13 = 27
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 255 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 13^2 = 255
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_06

theorem weighted_01_05_01_06 : b4RawGapContribution ![1, 5, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 6] = b4GapPatternWeight 5 1 6 * 0 :=
      b4GapContribution_from_row 1 5 1 6 0 row_01_05_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_06

def layers_01_05_01_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 14, 13, 11, 9, 7, 5, 3, 1, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 36, 49, 63, 76, 87, 96, 103, 108, 111, 112, 111, 108, 103, 96]]
#print axioms Paper7MomentGapNumeric.layers_01_05_01_07

theorem cells_01_05_01_07 : QTableValid (![1, 6, 7, 14] : Fin 4 → ℕ) layers_01_05_01_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_05_01_07

theorem valid_01_05_01_07 :
    SparseRowValid (![1, 6, 7, 14] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_05_01_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 6, 7, 14] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 1 + 6 + 7 + 14 = 28
      decide
    have hzsq : (∑ i, (((![1, 6, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 282 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 6^2 + 7^2 + 14^2 = 282
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_05_01_07
#print axioms Paper7MomentGapNumeric.valid_01_05_01_07

def qvalues_01_05_01_07 : Fin 19 → ℕ := ![0, 0, 0, 16, 0, 0, 0, 0, 0, 87, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_05_01_07

theorem row_01_05_01_07 : b4RowContribution (![1, 6, 7, 14] : Fin 4 → ℕ) = 103 := by
  calc
    b4RowContribution (![1, 6, 7, 14] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_05_01_07) :=
      sparseRow_sound (![1, 6, 7, 14] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_05_01_07) valid_01_05_01_07
    _ = 103 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_05_01_07 Q := by
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
        _ = 103 := by decide
#print axioms Paper7MomentGapNumeric.row_01_05_01_07

theorem weighted_01_05_01_07 : b4RawGapContribution ![1, 5, 1, 7] = 2472 := by
  calc
    b4RawGapContribution ![1, 5, 1, 7] = b4GapPatternWeight 5 1 7 * 103 :=
      b4GapContribution_from_row 1 5 1 7 103 row_01_05_01_07
    _ = 2472 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_07

theorem row_01_05_01_08 : b4RowContribution (![1, 6, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 15 = 29
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 311 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 15^2 = 311
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_08

theorem weighted_01_05_01_08 : b4RawGapContribution ![1, 5, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 8] = b4GapPatternWeight 5 1 8 * 0 :=
      b4GapContribution_from_row 1 5 1 8 0 row_01_05_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_08

theorem row_01_05_01_09 : b4RowContribution (![1, 6, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 16 = 30
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 16^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_09

theorem weighted_01_05_01_09 : b4RawGapContribution ![1, 5, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 9] = b4GapPatternWeight 5 1 9 * 0 :=
      b4GapContribution_from_row 1 5 1 9 0 row_01_05_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_09

theorem row_01_05_01_10 : b4RowContribution (![1, 6, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 17 = 31
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 375 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 17^2 = 375
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_10

theorem weighted_01_05_01_10 : b4RawGapContribution ![1, 5, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 10] = b4GapPatternWeight 5 1 10 * 0 :=
      b4GapContribution_from_row 1 5 1 10 0 row_01_05_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_10

theorem row_01_05_01_11 : b4RowContribution (![1, 6, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 18 = 32
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 410 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 18^2 = 410
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_11

theorem weighted_01_05_01_11 : b4RawGapContribution ![1, 5, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 11] = b4GapPatternWeight 5 1 11 * 0 :=
      b4GapContribution_from_row 1 5 1 11 0 row_01_05_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_11

theorem row_01_05_01_12 : b4RowContribution (![1, 6, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 19 = 33
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 447 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 19^2 = 447
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_12

theorem weighted_01_05_01_12 : b4RawGapContribution ![1, 5, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 12] = b4GapPatternWeight 5 1 12 * 0 :=
      b4GapContribution_from_row 1 5 1 12 0 row_01_05_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_12

theorem row_01_05_01_13 : b4RowContribution (![1, 6, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 20 = 34
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 486 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 20^2 = 486
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_13

theorem weighted_01_05_01_13 : b4RawGapContribution ![1, 5, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 13] = b4GapPatternWeight 5 1 13 * 0 :=
      b4GapContribution_from_row 1 5 1 13 0 row_01_05_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_13

theorem row_01_05_01_14 : b4RowContribution (![1, 6, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 21 = 35
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 527 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 21^2 = 527
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_14

theorem weighted_01_05_01_14 : b4RawGapContribution ![1, 5, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 14] = b4GapPatternWeight 5 1 14 * 0 :=
      b4GapContribution_from_row 1 5 1 14 0 row_01_05_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_14

theorem row_01_05_01_15 : b4RowContribution (![1, 6, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 22 = 36
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 570 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 22^2 = 570
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_15

theorem weighted_01_05_01_15 : b4RawGapContribution ![1, 5, 1, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 15] = b4GapPatternWeight 5 1 15 * 0 :=
      b4GapContribution_from_row 1 5 1 15 0 row_01_05_01_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_15

theorem row_01_05_01_16 : b4RowContribution (![1, 6, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 7, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 7 + 23 = 37
    decide
  have hzsq : (∑ i, (((![1, 6, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 615 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 7^2 + 23^2 = 615
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_01_16

theorem weighted_01_05_01_16 : b4RawGapContribution ![1, 5, 1, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 1, 16] = b4GapPatternWeight 5 1 16 * 0 :=
      b4GapContribution_from_row 1 5 1 16 0 row_01_05_01_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_01_16

def dvalues_01_05_01 : Fin 17 → ℕ := ![0, 0, 0, 0, 0, 1824, 0, 2472, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_05_01

theorem dblock_01_05_01 : b4GapPatternDBlock 1 5 1 = 4296 := by
  calc
    b4GapPatternDBlock 1 5 1 = ∑ d : Fin 17, dvalues_01_05_01 d := by
      apply b4GapDBlock_of_rows 1 5 1 dvalues_01_05_01
      intro d
      fin_cases d
      · exact weighted_01_05_01_00
      · exact weighted_01_05_01_01
      · exact weighted_01_05_01_02
      · exact weighted_01_05_01_03
      · exact weighted_01_05_01_04
      · exact weighted_01_05_01_05
      · exact weighted_01_05_01_06
      · exact weighted_01_05_01_07
      · exact weighted_01_05_01_08
      · exact weighted_01_05_01_09
      · exact weighted_01_05_01_10
      · exact weighted_01_05_01_11
      · exact weighted_01_05_01_12
      · exact weighted_01_05_01_13
      · exact weighted_01_05_01_14
      · exact weighted_01_05_01_15
      · exact weighted_01_05_01_16
    _ = 4296 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_05_01

end Paper7MomentGapNumeric
