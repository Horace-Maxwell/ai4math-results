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

theorem row_01_03_04_00 : b4RowContribution (![1, 4, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 8, 8] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 8 + 8 = 21
    decide
  have hzsq : (∑ i, (((![1, 4, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 145 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 8^2 + 8^2 = 145
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_04_00

theorem weighted_01_03_04_00 : b4RawGapContribution ![1, 3, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 4, 0] = b4GapPatternWeight 3 4 0 * 0 :=
      b4GapContribution_from_row 1 3 4 0 0 row_01_03_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_00

theorem row_01_03_04_01 : b4RowContribution (![1, 4, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 8, 9] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 8 + 9 = 22
    decide
  have hzsq : (∑ i, (((![1, 4, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 162 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 8^2 + 9^2 = 162
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_04_01

theorem weighted_01_03_04_01 : b4RawGapContribution ![1, 3, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 4, 1] = b4GapPatternWeight 3 4 1 * 0 :=
      b4GapContribution_from_row 1 3 4 1 0 row_01_03_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_01

theorem row_01_03_04_02 : b4RowContribution (![1, 4, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 8, 10] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 8 + 10 = 23
    decide
  have hzsq : (∑ i, (((![1, 4, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 181 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 8^2 + 10^2 = 181
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_04_02

theorem weighted_01_03_04_02 : b4RawGapContribution ![1, 3, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 4, 2] = b4GapPatternWeight 3 4 2 * 0 :=
      b4GapContribution_from_row 1 3 4 2 0 row_01_03_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_02

theorem row_01_03_04_03 : b4RowContribution (![1, 4, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 8, 11] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 8 + 11 = 24
    decide
  have hzsq : (∑ i, (((![1, 4, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 202 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 8^2 + 11^2 = 202
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_04_03

theorem weighted_01_03_04_03 : b4RawGapContribution ![1, 3, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 4, 3] = b4GapPatternWeight 3 4 3 * 0 :=
      b4GapContribution_from_row 1 3 4 3 0 row_01_03_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_03

def layers_01_03_04_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 10, 10, 10, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 35, 45, 55, 65, 74, 81, 86, 89, 89, 86, 81, 74, 65, 55]]
#print axioms Paper7MomentGapNumeric.layers_01_03_04_04

theorem cells_01_03_04_04 : QTableValid (![1, 4, 8, 12] : Fin 4 → ℕ) layers_01_03_04_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_04_04

theorem valid_01_03_04_04 :
    SparseRowValid (![1, 4, 8, 12] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_01_03_04_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 8, 12] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 8 + 12 = 25
      decide
    have hzsq : (∑ i, (((![1, 4, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 225 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 8^2 + 12^2 = 225
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_04_04
#print axioms Paper7MomentGapNumeric.valid_01_03_04_04

def qvalues_01_03_04_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 45, 0, 0, 0, 0, 0, 89, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_04_04

theorem row_01_03_04_04 : b4RowContribution (![1, 4, 8, 12] : Fin 4 → ℕ) = 134 := by
  calc
    b4RowContribution (![1, 4, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({6, 12} : Finset (Fin 19)) (fun _ => layers_01_03_04_04) :=
      sparseRow_sound (![1, 4, 8, 12] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_01_03_04_04) valid_01_03_04_04
    _ = 134 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_04_04 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 134 := by decide
#print axioms Paper7MomentGapNumeric.row_01_03_04_04

theorem weighted_01_03_04_04 : b4RawGapContribution ![1, 3, 4, 4] = 3216 := by
  calc
    b4RawGapContribution ![1, 3, 4, 4] = b4GapPatternWeight 3 4 4 * 134 :=
      b4GapContribution_from_row 1 3 4 4 134 row_01_03_04_04
    _ = 3216 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_04

theorem row_01_03_04_05 : b4RowContribution (![1, 4, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 8, 13] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 8 + 13 = 26
    decide
  have hzsq : (∑ i, (((![1, 4, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 250 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 8^2 + 13^2 = 250
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_04_05

theorem weighted_01_03_04_05 : b4RawGapContribution ![1, 3, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 4, 5] = b4GapPatternWeight 3 4 5 * 0 :=
      b4GapContribution_from_row 1 3 4 5 0 row_01_03_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_05

def layers_01_03_04_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 10, 10, 10, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 35, 45, 55, 65, 74, 81, 86, 89, 90, 90, 89, 86, 81, 74]]
#print axioms Paper7MomentGapNumeric.layers_01_03_04_06

theorem cells_01_03_04_06 : QTableValid (![1, 4, 8, 14] : Fin 4 → ℕ) layers_01_03_04_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_04_06

theorem valid_01_03_04_06 :
    SparseRowValid (![1, 4, 8, 14] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_03_04_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 8, 14] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 8 + 14 = 27
      decide
    have hzsq : (∑ i, (((![1, 4, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 277 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 8^2 + 14^2 = 277
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_04_06
#print axioms Paper7MomentGapNumeric.valid_01_03_04_06

def qvalues_01_03_04_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_04_06

theorem row_01_03_04_06 : b4RowContribution (![1, 4, 8, 14] : Fin 4 → ℕ) = 55 := by
  calc
    b4RowContribution (![1, 4, 8, 14] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_01_03_04_06) :=
      sparseRow_sound (![1, 4, 8, 14] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_03_04_06) valid_01_03_04_06
    _ = 55 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_04_06 Q := by
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
        _ = 55 := by decide
#print axioms Paper7MomentGapNumeric.row_01_03_04_06

theorem weighted_01_03_04_06 : b4RawGapContribution ![1, 3, 4, 6] = 1320 := by
  calc
    b4RawGapContribution ![1, 3, 4, 6] = b4GapPatternWeight 3 4 6 * 55 :=
      b4GapContribution_from_row 1 3 4 6 55 row_01_03_04_06
    _ = 1320 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_06

theorem row_01_03_04_07 : b4RowContribution (![1, 4, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 8, 15] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 8 + 15 = 28
    decide
  have hzsq : (∑ i, (((![1, 4, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 8^2 + 15^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_04_07

theorem weighted_01_03_04_07 : b4RawGapContribution ![1, 3, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 4, 7] = b4GapPatternWeight 3 4 7 * 0 :=
      b4GapContribution_from_row 1 3 4 7 0 row_01_03_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_07

theorem row_01_03_04_08 : b4RowContribution (![1, 4, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 8, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 8 + 16 = 29
    decide
  have hzsq : (∑ i, (((![1, 4, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 337 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 8^2 + 16^2 = 337
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_04_08

theorem weighted_01_03_04_08 : b4RawGapContribution ![1, 3, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 4, 8] = b4GapPatternWeight 3 4 8 * 0 :=
      b4GapContribution_from_row 1 3 4 8 0 row_01_03_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_08

theorem row_01_03_04_09 : b4RowContribution (![1, 4, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 8, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 8 + 17 = 30
    decide
  have hzsq : (∑ i, (((![1, 4, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 370 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 8^2 + 17^2 = 370
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_04_09

theorem weighted_01_03_04_09 : b4RawGapContribution ![1, 3, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 4, 9] = b4GapPatternWeight 3 4 9 * 0 :=
      b4GapContribution_from_row 1 3 4 9 0 row_01_03_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_09

theorem row_01_03_04_10 : b4RowContribution (![1, 4, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 8, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 8 + 18 = 31
    decide
  have hzsq : (∑ i, (((![1, 4, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 405 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 8^2 + 18^2 = 405
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_04_10

theorem weighted_01_03_04_10 : b4RawGapContribution ![1, 3, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 4, 10] = b4GapPatternWeight 3 4 10 * 0 :=
      b4GapContribution_from_row 1 3 4 10 0 row_01_03_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_10

theorem row_01_03_04_11 : b4RowContribution (![1, 4, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 8, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 8 + 19 = 32
    decide
  have hzsq : (∑ i, (((![1, 4, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 442 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 8^2 + 19^2 = 442
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_04_11

theorem weighted_01_03_04_11 : b4RawGapContribution ![1, 3, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 4, 11] = b4GapPatternWeight 3 4 11 * 0 :=
      b4GapContribution_from_row 1 3 4 11 0 row_01_03_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_11

theorem row_01_03_04_12 : b4RowContribution (![1, 4, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 8, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 8 + 20 = 33
    decide
  have hzsq : (∑ i, (((![1, 4, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 481 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 8^2 + 20^2 = 481
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_04_12

theorem weighted_01_03_04_12 : b4RawGapContribution ![1, 3, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 4, 12] = b4GapPatternWeight 3 4 12 * 0 :=
      b4GapContribution_from_row 1 3 4 12 0 row_01_03_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_12

theorem row_01_03_04_13 : b4RowContribution (![1, 4, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 8, 21] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 8 + 21 = 34
    decide
  have hzsq : (∑ i, (((![1, 4, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 522 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 8^2 + 21^2 = 522
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_04_13

theorem weighted_01_03_04_13 : b4RawGapContribution ![1, 3, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 4, 13] = b4GapPatternWeight 3 4 13 * 0 :=
      b4GapContribution_from_row 1 3 4 13 0 row_01_03_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_13

def layers_01_03_04_14 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 10, 10, 10, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 35, 45, 55, 65, 74, 81, 86, 89, 90, 90, 90, 90, 90, 90]]
#print axioms Paper7MomentGapNumeric.layers_01_03_04_14

theorem cells_01_03_04_14 : QTableValid (![1, 4, 8, 22] : Fin 4 → ℕ) layers_01_03_04_14 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_04_14

theorem valid_01_03_04_14 :
    SparseRowValid (![1, 4, 8, 22] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_01_03_04_14) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 8, 22] : Fin 4 → ℕ) i) = 35 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 8 + 22 = 35
      decide
    have hzsq : (∑ i, (((![1, 4, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 565 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 8^2 + 22^2 = 565
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_04_14
#print axioms Paper7MomentGapNumeric.valid_01_03_04_14

def qvalues_01_03_04_14 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_04_14

theorem row_01_03_04_14 : b4RowContribution (![1, 4, 8, 22] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![1, 4, 8, 22] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_01_03_04_14) :=
      sparseRow_sound (![1, 4, 8, 22] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_01_03_04_14) valid_01_03_04_14
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_04_14 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.row_01_03_04_14

theorem weighted_01_03_04_14 : b4RawGapContribution ![1, 3, 4, 14] = 96 := by
  calc
    b4RawGapContribution ![1, 3, 4, 14] = b4GapPatternWeight 3 4 14 * 4 :=
      b4GapContribution_from_row 1 3 4 14 4 row_01_03_04_14
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_14

theorem row_01_03_04_15 : b4RowContribution (![1, 4, 8, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 8, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 8 + 23 = 36
    decide
  have hzsq : (∑ i, (((![1, 4, 8, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 610 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 8^2 + 23^2 = 610
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_04_15

theorem weighted_01_03_04_15 : b4RawGapContribution ![1, 3, 4, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 4, 15] = b4GapPatternWeight 3 4 15 * 0 :=
      b4GapContribution_from_row 1 3 4 15 0 row_01_03_04_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_15

theorem row_01_03_04_16 : b4RowContribution (![1, 4, 8, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 8, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 8 + 24 = 37
    decide
  have hzsq : (∑ i, (((![1, 4, 8, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 657 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 8^2 + 24^2 = 657
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_04_16

theorem weighted_01_03_04_16 : b4RawGapContribution ![1, 3, 4, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 4, 16] = b4GapPatternWeight 3 4 16 * 0 :=
      b4GapContribution_from_row 1 3 4 16 0 row_01_03_04_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_04_16

def dvalues_01_03_04 : Fin 17 → ℕ := ![0, 0, 0, 0, 3216, 0, 1320, 0, 0, 0, 0, 0, 0, 0, 96, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_03_04

theorem dblock_01_03_04 : b4GapPatternDBlock 1 3 4 = 4632 := by
  calc
    b4GapPatternDBlock 1 3 4 = ∑ d : Fin 17, dvalues_01_03_04 d := by
      apply b4GapDBlock_of_rows 1 3 4 dvalues_01_03_04
      intro d
      fin_cases d
      · exact weighted_01_03_04_00
      · exact weighted_01_03_04_01
      · exact weighted_01_03_04_02
      · exact weighted_01_03_04_03
      · exact weighted_01_03_04_04
      · exact weighted_01_03_04_05
      · exact weighted_01_03_04_06
      · exact weighted_01_03_04_07
      · exact weighted_01_03_04_08
      · exact weighted_01_03_04_09
      · exact weighted_01_03_04_10
      · exact weighted_01_03_04_11
      · exact weighted_01_03_04_12
      · exact weighted_01_03_04_13
      · exact weighted_01_03_04_14
      · exact weighted_01_03_04_15
      · exact weighted_01_03_04_16
    _ = 4632 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_03_04

end Paper7MomentGapNumeric
