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

theorem row_00_05_04_00 : b4RowContribution (![0, 5, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 9, 9] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 9 + 9 = 23
    decide
  have hzsq : (∑ i, (((![0, 5, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 187 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 9^2 + 9^2 = 187
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_04_00

theorem weighted_00_05_04_00 : b4RawGapContribution ![0, 5, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 4, 0] = b4GapPatternWeight 5 4 0 * 0 :=
      b4GapContribution_from_row 0 5 4 0 0 row_00_05_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_00

theorem row_00_05_04_01 : b4RowContribution (![0, 5, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 9, 10] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 9 + 10 = 24
    decide
  have hzsq : (∑ i, (((![0, 5, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 206 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 9^2 + 10^2 = 206
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_04_01

theorem weighted_00_05_04_01 : b4RawGapContribution ![0, 5, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 4, 1] = b4GapPatternWeight 5 4 1 * 0 :=
      b4GapContribution_from_row 0 5 4 1 0 row_00_05_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_01

def layers_00_05_04_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 6, 6, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 27, 33, 39, 45, 50, 54, 56, 56, 54, 50, 45, 39, 33]]
#print axioms Paper7MomentGapNumeric.layers_00_05_04_02

theorem cells_00_05_04_02 : QTableValid (![0, 5, 9, 11] : Fin 4 → ℕ) layers_00_05_04_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_05_04_02

theorem valid_00_05_04_02 :
    SparseRowValid (![0, 5, 9, 11] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_00_05_04_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 5, 9, 11] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 5 + 9 + 11 = 25
      decide
    have hzsq : (∑ i, (((![0, 5, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 227 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 5^2 + 9^2 + 11^2 = 227
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_05_04_02
#print axioms Paper7MomentGapNumeric.valid_00_05_04_02

def qvalues_00_05_04_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_05_04_02

theorem row_00_05_04_02 : b4RowContribution (![0, 5, 9, 11] : Fin 4 → ℕ) = 75 := by
  calc
    b4RowContribution (![0, 5, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({5, 11} : Finset (Fin 19)) (fun _ => layers_00_05_04_02) :=
      sparseRow_sound (![0, 5, 9, 11] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_00_05_04_02) valid_00_05_04_02
    _ = 75 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_05_04_02 Q := by
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
        _ = 75 := by decide
#print axioms Paper7MomentGapNumeric.row_00_05_04_02

theorem weighted_00_05_04_02 : b4RawGapContribution ![0, 5, 4, 2] = 1800 := by
  calc
    b4RawGapContribution ![0, 5, 4, 2] = b4GapPatternWeight 5 4 2 * 75 :=
      b4GapContribution_from_row 0 5 4 2 75 row_00_05_04_02
    _ = 1800 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_02

theorem row_00_05_04_03 : b4RowContribution (![0, 5, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 9, 12] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 9 + 12 = 26
    decide
  have hzsq : (∑ i, (((![0, 5, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 250 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 9^2 + 12^2 = 250
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_04_03

theorem weighted_00_05_04_03 : b4RawGapContribution ![0, 5, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 4, 3] = b4GapPatternWeight 5 4 3 * 0 :=
      b4GapContribution_from_row 0 5 4 3 0 row_00_05_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_03

def layers_00_05_04_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 6, 6, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 27, 33, 39, 45, 50, 54, 57, 59, 59, 57, 54, 50, 45]]
#print axioms Paper7MomentGapNumeric.layers_00_05_04_04

theorem cells_00_05_04_04 : QTableValid (![0, 5, 9, 13] : Fin 4 → ℕ) layers_00_05_04_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_05_04_04

theorem valid_00_05_04_04 :
    SparseRowValid (![0, 5, 9, 13] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_05_04_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 5, 9, 13] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 0 + 5 + 9 + 13 = 27
      decide
    have hzsq : (∑ i, (((![0, 5, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 275 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 5^2 + 9^2 + 13^2 = 275
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_05_04_04
#print axioms Paper7MomentGapNumeric.valid_00_05_04_04

def qvalues_00_05_04_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_05_04_04

theorem row_00_05_04_04 : b4RowContribution (![0, 5, 9, 13] : Fin 4 → ℕ) = 39 := by
  calc
    b4RowContribution (![0, 5, 9, 13] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_00_05_04_04) :=
      sparseRow_sound (![0, 5, 9, 13] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_05_04_04) valid_00_05_04_04
    _ = 39 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_05_04_04 Q := by
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
        _ = 39 := by decide
#print axioms Paper7MomentGapNumeric.row_00_05_04_04

theorem weighted_00_05_04_04 : b4RawGapContribution ![0, 5, 4, 4] = 936 := by
  calc
    b4RawGapContribution ![0, 5, 4, 4] = b4GapPatternWeight 5 4 4 * 39 :=
      b4GapContribution_from_row 0 5 4 4 39 row_00_05_04_04
    _ = 936 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_04

theorem row_00_05_04_05 : b4RowContribution (![0, 5, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 9, 14] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 9 + 14 = 28
    decide
  have hzsq : (∑ i, (((![0, 5, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 302 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 9^2 + 14^2 = 302
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_04_05

theorem weighted_00_05_04_05 : b4RawGapContribution ![0, 5, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 4, 5] = b4GapPatternWeight 5 4 5 * 0 :=
      b4GapContribution_from_row 0 5 4 5 0 row_00_05_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_05

theorem row_00_05_04_06 : b4RowContribution (![0, 5, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 9, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 9 + 15 = 29
    decide
  have hzsq : (∑ i, (((![0, 5, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 331 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 9^2 + 15^2 = 331
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_04_06

theorem weighted_00_05_04_06 : b4RawGapContribution ![0, 5, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 4, 6] = b4GapPatternWeight 5 4 6 * 0 :=
      b4GapContribution_from_row 0 5 4 6 0 row_00_05_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_06

theorem row_00_05_04_07 : b4RowContribution (![0, 5, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 9, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 9 + 16 = 30
    decide
  have hzsq : (∑ i, (((![0, 5, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 362 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 9^2 + 16^2 = 362
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_04_07

theorem weighted_00_05_04_07 : b4RawGapContribution ![0, 5, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 4, 7] = b4GapPatternWeight 5 4 7 * 0 :=
      b4GapContribution_from_row 0 5 4 7 0 row_00_05_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_07

theorem row_00_05_04_08 : b4RowContribution (![0, 5, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 9, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 9 + 17 = 31
    decide
  have hzsq : (∑ i, (((![0, 5, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 395 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 9^2 + 17^2 = 395
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_04_08

theorem weighted_00_05_04_08 : b4RawGapContribution ![0, 5, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 4, 8] = b4GapPatternWeight 5 4 8 * 0 :=
      b4GapContribution_from_row 0 5 4 8 0 row_00_05_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_08

theorem row_00_05_04_09 : b4RowContribution (![0, 5, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 9, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 9 + 18 = 32
    decide
  have hzsq : (∑ i, (((![0, 5, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 430 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 9^2 + 18^2 = 430
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_04_09

theorem weighted_00_05_04_09 : b4RawGapContribution ![0, 5, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 4, 9] = b4GapPatternWeight 5 4 9 * 0 :=
      b4GapContribution_from_row 0 5 4 9 0 row_00_05_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_09

theorem row_00_05_04_10 : b4RowContribution (![0, 5, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 9, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 9 + 19 = 33
    decide
  have hzsq : (∑ i, (((![0, 5, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 467 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 9^2 + 19^2 = 467
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_04_10

theorem weighted_00_05_04_10 : b4RawGapContribution ![0, 5, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 4, 10] = b4GapPatternWeight 5 4 10 * 0 :=
      b4GapContribution_from_row 0 5 4 10 0 row_00_05_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_10

theorem row_00_05_04_11 : b4RowContribution (![0, 5, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 9, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 9 + 20 = 34
    decide
  have hzsq : (∑ i, (((![0, 5, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 506 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 9^2 + 20^2 = 506
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_04_11

theorem weighted_00_05_04_11 : b4RawGapContribution ![0, 5, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 4, 11] = b4GapPatternWeight 5 4 11 * 0 :=
      b4GapContribution_from_row 0 5 4 11 0 row_00_05_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_11

theorem row_00_05_04_12 : b4RowContribution (![0, 5, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 9, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 9 + 21 = 35
    decide
  have hzsq : (∑ i, (((![0, 5, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 547 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 9^2 + 21^2 = 547
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_04_12

theorem weighted_00_05_04_12 : b4RawGapContribution ![0, 5, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 4, 12] = b4GapPatternWeight 5 4 12 * 0 :=
      b4GapContribution_from_row 0 5 4 12 0 row_00_05_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_12

theorem row_00_05_04_13 : b4RowContribution (![0, 5, 9, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 9, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 9 + 22 = 36
    decide
  have hzsq : (∑ i, (((![0, 5, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 590 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 9^2 + 22^2 = 590
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_04_13

theorem weighted_00_05_04_13 : b4RawGapContribution ![0, 5, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 4, 13] = b4GapPatternWeight 5 4 13 * 0 :=
      b4GapContribution_from_row 0 5 4 13 0 row_00_05_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_13

theorem row_00_05_04_14 : b4RowContribution (![0, 5, 9, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 9, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 9 + 23 = 37
    decide
  have hzsq : (∑ i, (((![0, 5, 9, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 635 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 9^2 + 23^2 = 635
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_04_14

theorem weighted_00_05_04_14 : b4RawGapContribution ![0, 5, 4, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 4, 14] = b4GapPatternWeight 5 4 14 * 0 :=
      b4GapContribution_from_row 0 5 4 14 0 row_00_05_04_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_04_14

def dvalues_00_05_04 : Fin 15 → ℕ := ![0, 0, 1800, 0, 936, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_05_04

theorem dblock_00_05_04 : b4GapPatternDBlock 0 5 4 = 2736 := by
  calc
    b4GapPatternDBlock 0 5 4 = ∑ d : Fin 15, dvalues_00_05_04 d := by
      apply b4GapDBlock_of_rows 0 5 4 dvalues_00_05_04
      intro d
      fin_cases d
      · exact weighted_00_05_04_00
      · exact weighted_00_05_04_01
      · exact weighted_00_05_04_02
      · exact weighted_00_05_04_03
      · exact weighted_00_05_04_04
      · exact weighted_00_05_04_05
      · exact weighted_00_05_04_06
      · exact weighted_00_05_04_07
      · exact weighted_00_05_04_08
      · exact weighted_00_05_04_09
      · exact weighted_00_05_04_10
      · exact weighted_00_05_04_11
      · exact weighted_00_05_04_12
      · exact weighted_00_05_04_13
      · exact weighted_00_05_04_14
    _ = 2736 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_05_04

end Paper7MomentGapNumeric
