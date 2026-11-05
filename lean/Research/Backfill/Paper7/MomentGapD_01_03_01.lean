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

theorem row_01_03_01_00 : b4RowContribution (![1, 4, 5, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 5] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 5 = 15
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 67 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 5^2 = 67
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_00

theorem weighted_01_03_01_00 : b4RawGapContribution ![1, 3, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 0] = b4GapPatternWeight 3 1 0 * 0 :=
      b4GapContribution_from_row 1 3 1 0 0 row_01_03_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_00

theorem row_01_03_01_01 : b4RowContribution (![1, 4, 5, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 6] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 6 = 16
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 78 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 6^2 = 78
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_01

theorem weighted_01_03_01_01 : b4RawGapContribution ![1, 3, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 1] = b4GapPatternWeight 3 1 1 * 0 :=
      b4GapContribution_from_row 1 3 1 1 0 row_01_03_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_01

theorem row_01_03_01_02 : b4RowContribution (![1, 4, 5, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 7] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 7 = 17
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 91 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 7^2 = 91
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_02

theorem weighted_01_03_01_02 : b4RawGapContribution ![1, 3, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 2] = b4GapPatternWeight 3 1 2 * 0 :=
      b4GapContribution_from_row 1 3 1 2 0 row_01_03_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_02

theorem row_01_03_01_03 : b4RowContribution (![1, 4, 5, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 8] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 8 = 18
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 106 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 8^2 = 106
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_03

theorem weighted_01_03_01_03 : b4RawGapContribution ![1, 3, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 3] = b4GapPatternWeight 3 1 3 * 0 :=
      b4GapContribution_from_row 1 3 1 3 0 row_01_03_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_03

theorem row_01_03_01_04 : b4RowContribution (![1, 4, 5, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 9] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 9 = 19
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 123 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 9^2 = 123
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_04

theorem weighted_01_03_01_04 : b4RawGapContribution ![1, 3, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 4] = b4GapPatternWeight 3 1 4 * 0 :=
      b4GapContribution_from_row 1 3 1 4 0 row_01_03_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_04

theorem row_01_03_01_05 : b4RowContribution (![1, 4, 5, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 10] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 10 = 20
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 142 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 10^2 = 142
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_05

theorem weighted_01_03_01_05 : b4RawGapContribution ![1, 3, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 5] = b4GapPatternWeight 3 1 5 * 0 :=
      b4GapContribution_from_row 1 3 1 5 0 row_01_03_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_05

theorem row_01_03_01_06 : b4RowContribution (![1, 4, 5, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 11] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 11 = 21
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 163 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 11^2 = 163
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_06

theorem weighted_01_03_01_06 : b4RawGapContribution ![1, 3, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 6] = b4GapPatternWeight 3 1 6 * 0 :=
      b4GapContribution_from_row 1 3 1 6 0 row_01_03_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_06

def layers_01_03_01_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 35, 44, 51, 56, 59, 60, 60, 60, 59, 56, 51, 44, 35, 25]]
#print axioms Paper7MomentGapNumeric.layers_01_03_01_07

theorem cells_01_03_01_07 : QTableValid (![1, 4, 5, 12] : Fin 4 → ℕ) layers_01_03_01_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_01_07

theorem valid_01_03_01_07 :
    SparseRowValid (![1, 4, 5, 12] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_01_03_01_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 5, 12] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 5 + 12 = 22
      decide
    have hzsq : (∑ i, (((![1, 4, 5, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 186 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 5^2 + 12^2 = 186
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_01_07
#print axioms Paper7MomentGapNumeric.valid_01_03_01_07

def qvalues_01_03_01_07 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_01_07

theorem row_01_03_01_07 : b4RowContribution (![1, 4, 5, 12] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![1, 4, 5, 12] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_01_03_01_07) :=
      sparseRow_sound (![1, 4, 5, 12] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_01_03_01_07) valid_01_03_01_07
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_01_07 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 1 := by decide
#print axioms Paper7MomentGapNumeric.row_01_03_01_07

theorem weighted_01_03_01_07 : b4RawGapContribution ![1, 3, 1, 7] = 24 := by
  calc
    b4RawGapContribution ![1, 3, 1, 7] = b4GapPatternWeight 3 1 7 * 1 :=
      b4GapContribution_from_row 1 3 1 7 1 row_01_03_01_07
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_07

theorem row_01_03_01_08 : b4RowContribution (![1, 4, 5, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 13] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 13 = 23
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 211 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 13^2 = 211
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_08

theorem weighted_01_03_01_08 : b4RawGapContribution ![1, 3, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 8] = b4GapPatternWeight 3 1 8 * 0 :=
      b4GapContribution_from_row 1 3 1 8 0 row_01_03_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_08

def layers_01_03_01_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 35, 44, 51, 56, 59, 60, 60, 60, 60, 60, 59, 56, 51, 44]]
#print axioms Paper7MomentGapNumeric.layers_01_03_01_09

theorem cells_01_03_01_09 : QTableValid (![1, 4, 5, 14] : Fin 4 → ℕ) layers_01_03_01_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_01_09

theorem valid_01_03_01_09 :
    SparseRowValid (![1, 4, 5, 14] : Fin 4 → ℕ) ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_03_01_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 5, 14] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 5 + 14 = 24
      decide
    have hzsq : (∑ i, (((![1, 4, 5, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 238 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 5^2 + 14^2 = 238
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_01_09
#print axioms Paper7MomentGapNumeric.valid_01_03_01_09

def qvalues_01_03_01_09 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_01_09

theorem row_01_03_01_09 : b4RowContribution (![1, 4, 5, 14] : Fin 4 → ℕ) = 55 := by
  calc
    b4RowContribution (![1, 4, 5, 14] : Fin 4 → ℕ) =
        sparseRowValue ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_03_01_09) :=
      sparseRow_sound (![1, 4, 5, 14] : Fin 4 → ℕ) ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_03_01_09) valid_01_03_01_09
    _ = 55 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_01_09 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_03_01_09

theorem weighted_01_03_01_09 : b4RawGapContribution ![1, 3, 1, 9] = 1320 := by
  calc
    b4RawGapContribution ![1, 3, 1, 9] = b4GapPatternWeight 3 1 9 * 55 :=
      b4GapContribution_from_row 1 3 1 9 55 row_01_03_01_09
    _ = 1320 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_09

theorem row_01_03_01_10 : b4RowContribution (![1, 4, 5, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 15] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 15 = 25
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 267 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 15^2 = 267
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_10

theorem weighted_01_03_01_10 : b4RawGapContribution ![1, 3, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 10] = b4GapPatternWeight 3 1 10 * 0 :=
      b4GapContribution_from_row 1 3 1 10 0 row_01_03_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_10

theorem row_01_03_01_11 : b4RowContribution (![1, 4, 5, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 16] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 16 = 26
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 298 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 16^2 = 298
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_11

theorem weighted_01_03_01_11 : b4RawGapContribution ![1, 3, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 11] = b4GapPatternWeight 3 1 11 * 0 :=
      b4GapContribution_from_row 1 3 1 11 0 row_01_03_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_11

theorem row_01_03_01_12 : b4RowContribution (![1, 4, 5, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 17] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 17 = 27
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 331 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 17^2 = 331
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_12

theorem weighted_01_03_01_12 : b4RawGapContribution ![1, 3, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 12] = b4GapPatternWeight 3 1 12 * 0 :=
      b4GapContribution_from_row 1 3 1 12 0 row_01_03_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_12

theorem row_01_03_01_13 : b4RowContribution (![1, 4, 5, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 18] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 18 = 28
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 366 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 18^2 = 366
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_13

theorem weighted_01_03_01_13 : b4RawGapContribution ![1, 3, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 13] = b4GapPatternWeight 3 1 13 * 0 :=
      b4GapContribution_from_row 1 3 1 13 0 row_01_03_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_13

theorem row_01_03_01_14 : b4RowContribution (![1, 4, 5, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 19] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 19 = 29
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 403 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 19^2 = 403
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_14

theorem weighted_01_03_01_14 : b4RawGapContribution ![1, 3, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 14] = b4GapPatternWeight 3 1 14 * 0 :=
      b4GapContribution_from_row 1 3 1 14 0 row_01_03_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_14

theorem row_01_03_01_15 : b4RowContribution (![1, 4, 5, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 20] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 20 = 30
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 442 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 20^2 = 442
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_15

theorem weighted_01_03_01_15 : b4RawGapContribution ![1, 3, 1, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 15] = b4GapPatternWeight 3 1 15 * 0 :=
      b4GapContribution_from_row 1 3 1 15 0 row_01_03_01_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_15

theorem row_01_03_01_16 : b4RowContribution (![1, 4, 5, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 21] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 21 = 31
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 483 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 21^2 = 483
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_16

theorem weighted_01_03_01_16 : b4RawGapContribution ![1, 3, 1, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 16] = b4GapPatternWeight 3 1 16 * 0 :=
      b4GapContribution_from_row 1 3 1 16 0 row_01_03_01_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_16

theorem row_01_03_01_17 : b4RowContribution (![1, 4, 5, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 22] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 22 = 32
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 526 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 22^2 = 526
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_17

theorem weighted_01_03_01_17 : b4RawGapContribution ![1, 3, 1, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 17] = b4GapPatternWeight 3 1 17 * 0 :=
      b4GapContribution_from_row 1 3 1 17 0 row_01_03_01_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_17

def layers_01_03_01_18 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 35, 44, 51, 56, 59, 60, 60, 60, 60, 60, 60, 60, 60, 60]]
#print axioms Paper7MomentGapNumeric.layers_01_03_01_18

theorem cells_01_03_01_18 : QTableValid (![1, 4, 5, 23] : Fin 4 → ℕ) layers_01_03_01_18 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_01_18

theorem valid_01_03_01_18 :
    SparseRowValid (![1, 4, 5, 23] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_01_03_01_18) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 5, 23] : Fin 4 → ℕ) i) = 33 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 5 + 23 = 33
      decide
    have hzsq : (∑ i, (((![1, 4, 5, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 571 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 5^2 + 23^2 = 571
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_01_18
#print axioms Paper7MomentGapNumeric.valid_01_03_01_18

def qvalues_01_03_01_18 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_01_18

theorem row_01_03_01_18 : b4RowContribution (![1, 4, 5, 23] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![1, 4, 5, 23] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_01_03_01_18) :=
      sparseRow_sound (![1, 4, 5, 23] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_01_03_01_18) valid_01_03_01_18
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_01_18 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_03_01_18

theorem weighted_01_03_01_18 : b4RawGapContribution ![1, 3, 1, 18] = 96 := by
  calc
    b4RawGapContribution ![1, 3, 1, 18] = b4GapPatternWeight 3 1 18 * 4 :=
      b4GapContribution_from_row 1 3 1 18 4 row_01_03_01_18
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_18

theorem row_01_03_01_19 : b4RowContribution (![1, 4, 5, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 24] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 24 = 34
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 618 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 24^2 = 618
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_19

theorem weighted_01_03_01_19 : b4RawGapContribution ![1, 3, 1, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 19] = b4GapPatternWeight 3 1 19 * 0 :=
      b4GapContribution_from_row 1 3 1 19 0 row_01_03_01_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_19

theorem row_01_03_01_20 : b4RowContribution (![1, 4, 5, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 25] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 25 = 35
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 667 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 25^2 = 667
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_20

theorem weighted_01_03_01_20 : b4RawGapContribution ![1, 3, 1, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 20] = b4GapPatternWeight 3 1 20 * 0 :=
      b4GapContribution_from_row 1 3 1 20 0 row_01_03_01_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_20

def layers_01_03_01_21 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 35, 44, 51, 56, 59, 60, 60, 60, 60, 60, 60, 60, 60, 60]]
#print axioms Paper7MomentGapNumeric.layers_01_03_01_21

theorem cells_01_03_01_21 : QTableValid (![1, 4, 5, 26] : Fin 4 → ℕ) layers_01_03_01_21 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_01_21

theorem valid_01_03_01_21 :
    SparseRowValid (![1, 4, 5, 26] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_01_03_01_21) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 5, 26] : Fin 4 → ℕ) i) = 36 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 5 + 26 = 36
      decide
    have hzsq : (∑ i, (((![1, 4, 5, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 718 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 5^2 + 26^2 = 718
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_01_21
#print axioms Paper7MomentGapNumeric.valid_01_03_01_21

def qvalues_01_03_01_21 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_01_21

theorem row_01_03_01_21 : b4RowContribution (![1, 4, 5, 26] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![1, 4, 5, 26] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_01_03_01_21) :=
      sparseRow_sound (![1, 4, 5, 26] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_01_03_01_21) valid_01_03_01_21
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_01_21 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_03_01_21

theorem weighted_01_03_01_21 : b4RawGapContribution ![1, 3, 1, 21] = 96 := by
  calc
    b4RawGapContribution ![1, 3, 1, 21] = b4GapPatternWeight 3 1 21 * 4 :=
      b4GapContribution_from_row 1 3 1 21 4 row_01_03_01_21
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_21

theorem row_01_03_01_22 : b4RowContribution (![1, 4, 5, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 5, 27] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 5 + 27 = 37
    decide
  have hzsq : (∑ i, (((![1, 4, 5, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 771 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 5^2 + 27^2 = 771
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_01_22

theorem weighted_01_03_01_22 : b4RawGapContribution ![1, 3, 1, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 1, 22] = b4GapPatternWeight 3 1 22 * 0 :=
      b4GapContribution_from_row 1 3 1 22 0 row_01_03_01_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_01_22

def dvalues_01_03_01 : Fin 23 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 24, 0, 1320, 0, 0, 0, 0, 0, 0, 0, 0, 96, 0, 0, 96, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_03_01

theorem dblock_01_03_01 : b4GapPatternDBlock 1 3 1 = 1536 := by
  calc
    b4GapPatternDBlock 1 3 1 = ∑ d : Fin 23, dvalues_01_03_01 d := by
      apply b4GapDBlock_of_rows 1 3 1 dvalues_01_03_01
      intro d
      fin_cases d
      · exact weighted_01_03_01_00
      · exact weighted_01_03_01_01
      · exact weighted_01_03_01_02
      · exact weighted_01_03_01_03
      · exact weighted_01_03_01_04
      · exact weighted_01_03_01_05
      · exact weighted_01_03_01_06
      · exact weighted_01_03_01_07
      · exact weighted_01_03_01_08
      · exact weighted_01_03_01_09
      · exact weighted_01_03_01_10
      · exact weighted_01_03_01_11
      · exact weighted_01_03_01_12
      · exact weighted_01_03_01_13
      · exact weighted_01_03_01_14
      · exact weighted_01_03_01_15
      · exact weighted_01_03_01_16
      · exact weighted_01_03_01_17
      · exact weighted_01_03_01_18
      · exact weighted_01_03_01_19
      · exact weighted_01_03_01_20
      · exact weighted_01_03_01_21
      · exact weighted_01_03_01_22
    _ = 1536 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_03_01

end Paper7MomentGapNumeric
