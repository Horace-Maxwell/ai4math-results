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

theorem row_01_04_04_00 : b4RowContribution (![1, 5, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 9, 9] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 9 + 9 = 24
    decide
  have hzsq : (∑ i, (((![1, 5, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 188 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 9^2 + 9^2 = 188
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_04_00

theorem weighted_01_04_04_00 : b4RawGapContribution ![1, 4, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 4, 0] = b4GapPatternWeight 4 4 0 * 0 :=
      b4GapContribution_from_row 1 4 4 0 0 row_01_04_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_04_00

theorem row_01_04_04_01 : b4RowContribution (![1, 5, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 9, 10] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 9 + 10 = 25
    decide
  have hzsq : (∑ i, (((![1, 5, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 207 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 9^2 + 10^2 = 207
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_04_01

theorem weighted_01_04_04_01 : b4RawGapContribution ![1, 4, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 4, 1] = b4GapPatternWeight 4 4 1 * 0 :=
      b4GapContribution_from_row 1 4 4 1 0 row_01_04_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_04_01

def layers_01_04_04_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 12, 12, 12, 12, 11, 9, 7, 5, 3, 1, 0, 0, 0], ![1, 4, 9, 16, 25, 36, 48, 60, 72, 84, 95, 104, 110, 112, 110, 104, 95, 84, 72]]
#print axioms Paper7MomentGapNumeric.layers_01_04_04_02

theorem cells_01_04_04_02 : QTableValid (![1, 5, 9, 11] : Fin 4 → ℕ) layers_01_04_04_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_04_04_02

theorem valid_01_04_04_02 :
    SparseRowValid (![1, 5, 9, 11] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_04_04_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 5, 9, 11] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 1 + 5 + 9 + 11 = 26
      decide
    have hzsq : (∑ i, (((![1, 5, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 228 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 5^2 + 9^2 + 11^2 = 228
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_04_04_02
#print axioms Paper7MomentGapNumeric.valid_01_04_04_02

def qvalues_01_04_04_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_04_04_02

theorem row_01_04_04_02 : b4RowContribution (![1, 5, 9, 11] : Fin 4 → ℕ) = 84 := by
  calc
    b4RowContribution (![1, 5, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_04_04_02) :=
      sparseRow_sound (![1, 5, 9, 11] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_04_04_02) valid_01_04_04_02
    _ = 84 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_04_04_02 Q := by
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
        _ = 84 := by decide
#print axioms Paper7MomentGapNumeric.row_01_04_04_02

theorem weighted_01_04_04_02 : b4RawGapContribution ![1, 4, 4, 2] = 2016 := by
  calc
    b4RawGapContribution ![1, 4, 4, 2] = b4GapPatternWeight 4 4 2 * 84 :=
      b4GapContribution_from_row 1 4 4 2 84 row_01_04_04_02
    _ = 2016 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_04_02

theorem row_01_04_04_03 : b4RowContribution (![1, 5, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 9, 12] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 9 + 12 = 27
    decide
  have hzsq : (∑ i, (((![1, 5, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 251 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 9^2 + 12^2 = 251
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_04_03

theorem weighted_01_04_04_03 : b4RawGapContribution ![1, 4, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 4, 3] = b4GapPatternWeight 4 4 3 * 0 :=
      b4GapContribution_from_row 1 4 4 3 0 row_01_04_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_04_03

def layers_01_04_04_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 12, 12, 12, 12, 11, 9, 7, 5, 3, 1, 0, 0, 0], ![1, 4, 9, 16, 25, 36, 48, 60, 72, 84, 95, 104, 111, 116, 118, 116, 111, 104, 95]]
#print axioms Paper7MomentGapNumeric.layers_01_04_04_04

theorem cells_01_04_04_04 : QTableValid (![1, 5, 9, 13] : Fin 4 → ℕ) layers_01_04_04_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_04_04_04

theorem valid_01_04_04_04 :
    SparseRowValid (![1, 5, 9, 13] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_01_04_04_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 5, 9, 13] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 1 + 5 + 9 + 13 = 28
      decide
    have hzsq : (∑ i, (((![1, 5, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 276 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 5^2 + 9^2 + 13^2 = 276
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_04_04_04
#print axioms Paper7MomentGapNumeric.valid_01_04_04_04

def qvalues_01_04_04_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_04_04_04

theorem row_01_04_04_04 : b4RowContribution (![1, 5, 9, 13] : Fin 4 → ℕ) = 48 := by
  calc
    b4RowContribution (![1, 5, 9, 13] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_01_04_04_04) :=
      sparseRow_sound (![1, 5, 9, 13] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_01_04_04_04) valid_01_04_04_04
    _ = 48 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_04_04_04 Q := by
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
        _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.row_01_04_04_04

theorem weighted_01_04_04_04 : b4RawGapContribution ![1, 4, 4, 4] = 1152 := by
  calc
    b4RawGapContribution ![1, 4, 4, 4] = b4GapPatternWeight 4 4 4 * 48 :=
      b4GapContribution_from_row 1 4 4 4 48 row_01_04_04_04
    _ = 1152 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_04_04

theorem row_01_04_04_05 : b4RowContribution (![1, 5, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 9, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 9 + 14 = 29
    decide
  have hzsq : (∑ i, (((![1, 5, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 303 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 9^2 + 14^2 = 303
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_04_05

theorem weighted_01_04_04_05 : b4RawGapContribution ![1, 4, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 4, 5] = b4GapPatternWeight 4 4 5 * 0 :=
      b4GapContribution_from_row 1 4 4 5 0 row_01_04_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_04_05

theorem row_01_04_04_06 : b4RowContribution (![1, 5, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 9, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 9 + 15 = 30
    decide
  have hzsq : (∑ i, (((![1, 5, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 332 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 9^2 + 15^2 = 332
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_04_06

theorem weighted_01_04_04_06 : b4RawGapContribution ![1, 4, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 4, 6] = b4GapPatternWeight 4 4 6 * 0 :=
      b4GapContribution_from_row 1 4 4 6 0 row_01_04_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_04_06

theorem row_01_04_04_07 : b4RowContribution (![1, 5, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 9, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 9 + 16 = 31
    decide
  have hzsq : (∑ i, (((![1, 5, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 363 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 9^2 + 16^2 = 363
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_04_07

theorem weighted_01_04_04_07 : b4RawGapContribution ![1, 4, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 4, 7] = b4GapPatternWeight 4 4 7 * 0 :=
      b4GapContribution_from_row 1 4 4 7 0 row_01_04_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_04_07

theorem row_01_04_04_08 : b4RowContribution (![1, 5, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 9, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 9 + 17 = 32
    decide
  have hzsq : (∑ i, (((![1, 5, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 396 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 9^2 + 17^2 = 396
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_04_08

theorem weighted_01_04_04_08 : b4RawGapContribution ![1, 4, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 4, 8] = b4GapPatternWeight 4 4 8 * 0 :=
      b4GapContribution_from_row 1 4 4 8 0 row_01_04_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_04_08

theorem row_01_04_04_09 : b4RowContribution (![1, 5, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 9, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 9 + 18 = 33
    decide
  have hzsq : (∑ i, (((![1, 5, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 431 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 9^2 + 18^2 = 431
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_04_09

theorem weighted_01_04_04_09 : b4RawGapContribution ![1, 4, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 4, 9] = b4GapPatternWeight 4 4 9 * 0 :=
      b4GapContribution_from_row 1 4 4 9 0 row_01_04_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_04_09

theorem row_01_04_04_10 : b4RowContribution (![1, 5, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 9, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 9 + 19 = 34
    decide
  have hzsq : (∑ i, (((![1, 5, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 468 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 9^2 + 19^2 = 468
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_04_10

theorem weighted_01_04_04_10 : b4RawGapContribution ![1, 4, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 4, 10] = b4GapPatternWeight 4 4 10 * 0 :=
      b4GapContribution_from_row 1 4 4 10 0 row_01_04_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_04_10

theorem row_01_04_04_11 : b4RowContribution (![1, 5, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 9, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 9 + 20 = 35
    decide
  have hzsq : (∑ i, (((![1, 5, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 507 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 9^2 + 20^2 = 507
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_04_11

theorem weighted_01_04_04_11 : b4RawGapContribution ![1, 4, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 4, 11] = b4GapPatternWeight 4 4 11 * 0 :=
      b4GapContribution_from_row 1 4 4 11 0 row_01_04_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_04_11

theorem row_01_04_04_12 : b4RowContribution (![1, 5, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 9, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 9 + 21 = 36
    decide
  have hzsq : (∑ i, (((![1, 5, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 548 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 9^2 + 21^2 = 548
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_04_12

theorem weighted_01_04_04_12 : b4RawGapContribution ![1, 4, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 4, 12] = b4GapPatternWeight 4 4 12 * 0 :=
      b4GapContribution_from_row 1 4 4 12 0 row_01_04_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_04_12

theorem row_01_04_04_13 : b4RowContribution (![1, 5, 9, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 9, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 9 + 22 = 37
    decide
  have hzsq : (∑ i, (((![1, 5, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 591 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 9^2 + 22^2 = 591
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_04_13

theorem weighted_01_04_04_13 : b4RawGapContribution ![1, 4, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 4, 13] = b4GapPatternWeight 4 4 13 * 0 :=
      b4GapContribution_from_row 1 4 4 13 0 row_01_04_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_04_13

def dvalues_01_04_04 : Fin 14 → ℕ := ![0, 0, 2016, 0, 1152, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_04_04

theorem dblock_01_04_04 : b4GapPatternDBlock 1 4 4 = 3168 := by
  calc
    b4GapPatternDBlock 1 4 4 = ∑ d : Fin 14, dvalues_01_04_04 d := by
      apply b4GapDBlock_of_rows 1 4 4 dvalues_01_04_04
      intro d
      fin_cases d
      · exact weighted_01_04_04_00
      · exact weighted_01_04_04_01
      · exact weighted_01_04_04_02
      · exact weighted_01_04_04_03
      · exact weighted_01_04_04_04
      · exact weighted_01_04_04_05
      · exact weighted_01_04_04_06
      · exact weighted_01_04_04_07
      · exact weighted_01_04_04_08
      · exact weighted_01_04_04_09
      · exact weighted_01_04_04_10
      · exact weighted_01_04_04_11
      · exact weighted_01_04_04_12
      · exact weighted_01_04_04_13
    _ = 3168 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_04_04

end Paper7MomentGapNumeric
