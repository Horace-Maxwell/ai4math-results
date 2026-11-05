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

theorem row_03_01_05_00 : b4RowContribution (![3, 4, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 9, 9] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 9 + 9 = 25
    decide
  have hzsq : (∑ i, (((![3, 4, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 187 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 9^2 + 9^2 = 187
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_05_00

theorem weighted_03_01_05_00 : b4RawGapContribution ![3, 1, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 5, 0] = b4GapPatternWeight 1 5 0 * 0 :=
      b4GapContribution_from_row 3 1 5 0 0 row_03_01_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_05_00

theorem row_03_01_05_01 : b4RowContribution (![3, 4, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 9, 10] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 9 + 10 = 26
    decide
  have hzsq : (∑ i, (((![3, 4, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 206 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 9^2 + 10^2 = 206
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_05_01

theorem weighted_03_01_05_01 : b4RawGapContribution ![3, 1, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 5, 1] = b4GapPatternWeight 1 5 1 * 0 :=
      b4GapContribution_from_row 3 1 5 1 0 row_03_01_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_05_01

def layers_03_01_05_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 17, 19, 20, 20, 20, 19, 17, 14, 10, 6, 3, 1, 0, 0], ![1, 4, 10, 20, 34, 51, 70, 90, 110, 130, 149, 166, 179, 186, 186, 179, 166, 149, 130]]
#print axioms Paper7MomentGapNumeric.layers_03_01_05_02

theorem cells_03_01_05_02 : QTableValid (![3, 4, 9, 11] : Fin 4 → ℕ) layers_03_01_05_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_01_05_02

theorem valid_03_01_05_02 :
    SparseRowValid (![3, 4, 9, 11] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_03_01_05_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 4, 9, 11] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 3 + 4 + 9 + 11 = 27
      decide
    have hzsq : (∑ i, (((![3, 4, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 227 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 4^2 + 9^2 + 11^2 = 227
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_01_05_02
#print axioms Paper7MomentGapNumeric.valid_03_01_05_02

def qvalues_03_01_05_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_01_05_02

theorem row_03_01_05_02 : b4RowContribution (![3, 4, 9, 11] : Fin 4 → ℕ) = 110 := by
  calc
    b4RowContribution (![3, 4, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_03_01_05_02) :=
      sparseRow_sound (![3, 4, 9, 11] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_03_01_05_02) valid_03_01_05_02
    _ = 110 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_01_05_02 Q := by
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
#print axioms Paper7MomentGapNumeric.row_03_01_05_02

theorem weighted_03_01_05_02 : b4RawGapContribution ![3, 1, 5, 2] = 2640 := by
  calc
    b4RawGapContribution ![3, 1, 5, 2] = b4GapPatternWeight 1 5 2 * 110 :=
      b4GapContribution_from_row 3 1 5 2 110 row_03_01_05_02
    _ = 2640 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_05_02

theorem row_03_01_05_03 : b4RowContribution (![3, 4, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 9, 12] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 9 + 12 = 28
    decide
  have hzsq : (∑ i, (((![3, 4, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 250 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 9^2 + 12^2 = 250
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_05_03

theorem weighted_03_01_05_03 : b4RawGapContribution ![3, 1, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 5, 3] = b4GapPatternWeight 1 5 3 * 0 :=
      b4GapContribution_from_row 3 1 5 3 0 row_03_01_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_05_03

def layers_03_01_05_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 17, 19, 20, 20, 20, 19, 17, 14, 10, 6, 3, 1, 0, 0], ![1, 4, 10, 20, 34, 51, 70, 90, 110, 130, 149, 166, 180, 190, 195, 195, 190, 180, 166]]
#print axioms Paper7MomentGapNumeric.layers_03_01_05_04

theorem cells_03_01_05_04 : QTableValid (![3, 4, 9, 13] : Fin 4 → ℕ) layers_03_01_05_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_01_05_04

theorem valid_03_01_05_04 :
    SparseRowValid (![3, 4, 9, 13] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_01_05_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 4, 9, 13] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 3 + 4 + 9 + 13 = 29
      decide
    have hzsq : (∑ i, (((![3, 4, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 275 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 4^2 + 9^2 + 13^2 = 275
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_01_05_04
#print axioms Paper7MomentGapNumeric.valid_03_01_05_04

def qvalues_03_01_05_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_01_05_04

theorem row_03_01_05_04 : b4RowContribution (![3, 4, 9, 13] : Fin 4 → ℕ) = 51 := by
  calc
    b4RowContribution (![3, 4, 9, 13] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_03_01_05_04) :=
      sparseRow_sound (![3, 4, 9, 13] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_01_05_04) valid_03_01_05_04
    _ = 51 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_01_05_04 Q := by
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
        _ = 51 := by decide
#print axioms Paper7MomentGapNumeric.row_03_01_05_04

theorem weighted_03_01_05_04 : b4RawGapContribution ![3, 1, 5, 4] = 1224 := by
  calc
    b4RawGapContribution ![3, 1, 5, 4] = b4GapPatternWeight 1 5 4 * 51 :=
      b4GapContribution_from_row 3 1 5 4 51 row_03_01_05_04
    _ = 1224 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_05_04

theorem row_03_01_05_05 : b4RowContribution (![3, 4, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 9, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 9 + 14 = 30
    decide
  have hzsq : (∑ i, (((![3, 4, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 302 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 9^2 + 14^2 = 302
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_05_05

theorem weighted_03_01_05_05 : b4RawGapContribution ![3, 1, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 5, 5] = b4GapPatternWeight 1 5 5 * 0 :=
      b4GapContribution_from_row 3 1 5 5 0 row_03_01_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_05_05

theorem row_03_01_05_06 : b4RowContribution (![3, 4, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 9, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 9 + 15 = 31
    decide
  have hzsq : (∑ i, (((![3, 4, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 331 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 9^2 + 15^2 = 331
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_05_06

theorem weighted_03_01_05_06 : b4RawGapContribution ![3, 1, 5, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 5, 6] = b4GapPatternWeight 1 5 6 * 0 :=
      b4GapContribution_from_row 3 1 5 6 0 row_03_01_05_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_05_06

theorem row_03_01_05_07 : b4RowContribution (![3, 4, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 9, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 9 + 16 = 32
    decide
  have hzsq : (∑ i, (((![3, 4, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 362 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 9^2 + 16^2 = 362
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_05_07

theorem weighted_03_01_05_07 : b4RawGapContribution ![3, 1, 5, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 5, 7] = b4GapPatternWeight 1 5 7 * 0 :=
      b4GapContribution_from_row 3 1 5 7 0 row_03_01_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_05_07

theorem row_03_01_05_08 : b4RowContribution (![3, 4, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 9, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 9 + 17 = 33
    decide
  have hzsq : (∑ i, (((![3, 4, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 395 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 9^2 + 17^2 = 395
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_05_08

theorem weighted_03_01_05_08 : b4RawGapContribution ![3, 1, 5, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 5, 8] = b4GapPatternWeight 1 5 8 * 0 :=
      b4GapContribution_from_row 3 1 5 8 0 row_03_01_05_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_05_08

theorem row_03_01_05_09 : b4RowContribution (![3, 4, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 9, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 9 + 18 = 34
    decide
  have hzsq : (∑ i, (((![3, 4, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 430 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 9^2 + 18^2 = 430
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_05_09

theorem weighted_03_01_05_09 : b4RawGapContribution ![3, 1, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 5, 9] = b4GapPatternWeight 1 5 9 * 0 :=
      b4GapContribution_from_row 3 1 5 9 0 row_03_01_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_05_09

theorem row_03_01_05_10 : b4RowContribution (![3, 4, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 9, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 9 + 19 = 35
    decide
  have hzsq : (∑ i, (((![3, 4, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 467 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 9^2 + 19^2 = 467
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_05_10

theorem weighted_03_01_05_10 : b4RawGapContribution ![3, 1, 5, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 5, 10] = b4GapPatternWeight 1 5 10 * 0 :=
      b4GapContribution_from_row 3 1 5 10 0 row_03_01_05_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_05_10

theorem row_03_01_05_11 : b4RowContribution (![3, 4, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 9, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 9 + 20 = 36
    decide
  have hzsq : (∑ i, (((![3, 4, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 506 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 9^2 + 20^2 = 506
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_05_11

theorem weighted_03_01_05_11 : b4RawGapContribution ![3, 1, 5, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 5, 11] = b4GapPatternWeight 1 5 11 * 0 :=
      b4GapContribution_from_row 3 1 5 11 0 row_03_01_05_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_05_11

theorem row_03_01_05_12 : b4RowContribution (![3, 4, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 9, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 9 + 21 = 37
    decide
  have hzsq : (∑ i, (((![3, 4, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 547 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 9^2 + 21^2 = 547
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_05_12

theorem weighted_03_01_05_12 : b4RawGapContribution ![3, 1, 5, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 5, 12] = b4GapPatternWeight 1 5 12 * 0 :=
      b4GapContribution_from_row 3 1 5 12 0 row_03_01_05_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_05_12

def dvalues_03_01_05 : Fin 13 → ℕ := ![0, 0, 2640, 0, 1224, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_01_05

theorem dblock_03_01_05 : b4GapPatternDBlock 3 1 5 = 3864 := by
  calc
    b4GapPatternDBlock 3 1 5 = ∑ d : Fin 13, dvalues_03_01_05 d := by
      apply b4GapDBlock_of_rows 3 1 5 dvalues_03_01_05
      intro d
      fin_cases d
      · exact weighted_03_01_05_00
      · exact weighted_03_01_05_01
      · exact weighted_03_01_05_02
      · exact weighted_03_01_05_03
      · exact weighted_03_01_05_04
      · exact weighted_03_01_05_05
      · exact weighted_03_01_05_06
      · exact weighted_03_01_05_07
      · exact weighted_03_01_05_08
      · exact weighted_03_01_05_09
      · exact weighted_03_01_05_10
      · exact weighted_03_01_05_11
      · exact weighted_03_01_05_12
    _ = 3864 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_01_05

end Paper7MomentGapNumeric
