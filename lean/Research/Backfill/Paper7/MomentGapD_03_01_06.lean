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

def layers_03_01_06_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 17, 19, 20, 20, 20, 20, 19, 17, 14, 10, 6, 3, 1, 0], ![1, 4, 10, 20, 34, 51, 70, 90, 110, 130, 150, 168, 182, 190, 190, 182, 168, 150, 130]]
#print axioms Paper7MomentGapNumeric.layers_03_01_06_00

theorem cells_03_01_06_00 : QTableValid (![3, 4, 10, 10] : Fin 4 → ℕ) layers_03_01_06_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_01_06_00

theorem valid_03_01_06_00 :
    SparseRowValid (![3, 4, 10, 10] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_03_01_06_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 4, 10, 10] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 3 + 4 + 10 + 10 = 27
      decide
    have hzsq : (∑ i, (((![3, 4, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 225 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 4^2 + 10^2 + 10^2 = 225
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_01_06_00
#print axioms Paper7MomentGapNumeric.valid_03_01_06_00

def qvalues_03_01_06_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 130, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_01_06_00

theorem row_03_01_06_00 : b4RowContribution (![3, 4, 10, 10] : Fin 4 → ℕ) = 130 := by
  calc
    b4RowContribution (![3, 4, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_03_01_06_00) :=
      sparseRow_sound (![3, 4, 10, 10] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_03_01_06_00) valid_03_01_06_00
    _ = 130 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_01_06_00 Q := by
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
        _ = 130 := by decide
#print axioms Paper7MomentGapNumeric.row_03_01_06_00

theorem weighted_03_01_06_00 : b4RawGapContribution ![3, 1, 6, 0] = 1560 := by
  calc
    b4RawGapContribution ![3, 1, 6, 0] = b4GapPatternWeight 1 6 0 * 130 :=
      b4GapContribution_from_row 3 1 6 0 130 row_03_01_06_00
    _ = 1560 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_06_00

theorem row_03_01_06_01 : b4RowContribution (![3, 4, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 10, 11] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 10 + 11 = 28
    decide
  have hzsq : (∑ i, (((![3, 4, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 246 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 10^2 + 11^2 = 246
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_06_01

theorem weighted_03_01_06_01 : b4RawGapContribution ![3, 1, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 6, 1] = b4GapPatternWeight 1 6 1 * 0 :=
      b4GapContribution_from_row 3 1 6 1 0 row_03_01_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_06_01

def layers_03_01_06_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 17, 19, 20, 20, 20, 20, 19, 17, 14, 10, 6, 3, 1, 0], ![1, 4, 10, 20, 34, 51, 70, 90, 110, 130, 150, 169, 186, 199, 206, 206, 199, 186, 169]]
#print axioms Paper7MomentGapNumeric.layers_03_01_06_02

theorem cells_03_01_06_02 : QTableValid (![3, 4, 10, 12] : Fin 4 → ℕ) layers_03_01_06_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_01_06_02

theorem valid_03_01_06_02 :
    SparseRowValid (![3, 4, 10, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_03_01_06_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 4, 10, 12] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 3 + 4 + 10 + 12 = 29
      decide
    have hzsq : (∑ i, (((![3, 4, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 269 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 4^2 + 10^2 + 12^2 = 269
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_01_06_02
#print axioms Paper7MomentGapNumeric.valid_03_01_06_02

def qvalues_03_01_06_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_01_06_02

theorem row_03_01_06_02 : b4RowContribution (![3, 4, 10, 12] : Fin 4 → ℕ) = 110 := by
  calc
    b4RowContribution (![3, 4, 10, 12] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_03_01_06_02) :=
      sparseRow_sound (![3, 4, 10, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_03_01_06_02) valid_03_01_06_02
    _ = 110 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_01_06_02 Q := by
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
        _ = 110 := by decide
#print axioms Paper7MomentGapNumeric.row_03_01_06_02

theorem weighted_03_01_06_02 : b4RawGapContribution ![3, 1, 6, 2] = 2640 := by
  calc
    b4RawGapContribution ![3, 1, 6, 2] = b4GapPatternWeight 1 6 2 * 110 :=
      b4GapContribution_from_row 3 1 6 2 110 row_03_01_06_02
    _ = 2640 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_06_02

theorem row_03_01_06_03 : b4RowContribution (![3, 4, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 10, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 10 + 13 = 30
    decide
  have hzsq : (∑ i, (((![3, 4, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 294 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 10^2 + 13^2 = 294
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_06_03

theorem weighted_03_01_06_03 : b4RawGapContribution ![3, 1, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 6, 3] = b4GapPatternWeight 1 6 3 * 0 :=
      b4GapContribution_from_row 3 1 6 3 0 row_03_01_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_06_03

theorem row_03_01_06_04 : b4RowContribution (![3, 4, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 10, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 10 + 14 = 31
    decide
  have hzsq : (∑ i, (((![3, 4, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 321 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 10^2 + 14^2 = 321
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_06_04

theorem weighted_03_01_06_04 : b4RawGapContribution ![3, 1, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 6, 4] = b4GapPatternWeight 1 6 4 * 0 :=
      b4GapContribution_from_row 3 1 6 4 0 row_03_01_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_06_04

theorem row_03_01_06_05 : b4RowContribution (![3, 4, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 10, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 10 + 15 = 32
    decide
  have hzsq : (∑ i, (((![3, 4, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 350 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 10^2 + 15^2 = 350
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_06_05

theorem weighted_03_01_06_05 : b4RawGapContribution ![3, 1, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 6, 5] = b4GapPatternWeight 1 6 5 * 0 :=
      b4GapContribution_from_row 3 1 6 5 0 row_03_01_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_06_05

theorem row_03_01_06_06 : b4RowContribution (![3, 4, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 10, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 10 + 16 = 33
    decide
  have hzsq : (∑ i, (((![3, 4, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 381 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 10^2 + 16^2 = 381
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_06_06

theorem weighted_03_01_06_06 : b4RawGapContribution ![3, 1, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 6, 6] = b4GapPatternWeight 1 6 6 * 0 :=
      b4GapContribution_from_row 3 1 6 6 0 row_03_01_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_06_06

theorem row_03_01_06_07 : b4RowContribution (![3, 4, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 10, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 10 + 17 = 34
    decide
  have hzsq : (∑ i, (((![3, 4, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 414 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 10^2 + 17^2 = 414
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_06_07

theorem weighted_03_01_06_07 : b4RawGapContribution ![3, 1, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 6, 7] = b4GapPatternWeight 1 6 7 * 0 :=
      b4GapContribution_from_row 3 1 6 7 0 row_03_01_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_06_07

theorem row_03_01_06_08 : b4RowContribution (![3, 4, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 10, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 10 + 18 = 35
    decide
  have hzsq : (∑ i, (((![3, 4, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 449 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 10^2 + 18^2 = 449
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_06_08

theorem weighted_03_01_06_08 : b4RawGapContribution ![3, 1, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 6, 8] = b4GapPatternWeight 1 6 8 * 0 :=
      b4GapContribution_from_row 3 1 6 8 0 row_03_01_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_06_08

theorem row_03_01_06_09 : b4RowContribution (![3, 4, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 10, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 10 + 19 = 36
    decide
  have hzsq : (∑ i, (((![3, 4, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 486 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 10^2 + 19^2 = 486
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_06_09

theorem weighted_03_01_06_09 : b4RawGapContribution ![3, 1, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 6, 9] = b4GapPatternWeight 1 6 9 * 0 :=
      b4GapContribution_from_row 3 1 6 9 0 row_03_01_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_06_09

theorem row_03_01_06_10 : b4RowContribution (![3, 4, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 10, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 10 + 20 = 37
    decide
  have hzsq : (∑ i, (((![3, 4, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 525 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 10^2 + 20^2 = 525
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_06_10

theorem weighted_03_01_06_10 : b4RawGapContribution ![3, 1, 6, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 6, 10] = b4GapPatternWeight 1 6 10 * 0 :=
      b4GapContribution_from_row 3 1 6 10 0 row_03_01_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_06_10

def dvalues_03_01_06 : Fin 11 → ℕ := ![1560, 0, 2640, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_01_06

theorem dblock_03_01_06 : b4GapPatternDBlock 3 1 6 = 4200 := by
  calc
    b4GapPatternDBlock 3 1 6 = ∑ d : Fin 11, dvalues_03_01_06 d := by
      apply b4GapDBlock_of_rows 3 1 6 dvalues_03_01_06
      intro d
      fin_cases d
      · exact weighted_03_01_06_00
      · exact weighted_03_01_06_01
      · exact weighted_03_01_06_02
      · exact weighted_03_01_06_03
      · exact weighted_03_01_06_04
      · exact weighted_03_01_06_05
      · exact weighted_03_01_06_06
      · exact weighted_03_01_06_07
      · exact weighted_03_01_06_08
      · exact weighted_03_01_06_09
      · exact weighted_03_01_06_10
    _ = 4200 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_01_06

end Paper7MomentGapNumeric
