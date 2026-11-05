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

theorem row_02_02_03_00 : b4RowContribution (![2, 4, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 7] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 7 = 20
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 118 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 7^2 = 118
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_00

theorem weighted_02_02_03_00 : b4RawGapContribution ![2, 2, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 0] = b4GapPatternWeight 2 3 0 * 0 :=
      b4GapContribution_from_row 2 2 3 0 0 row_02_02_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_00

theorem row_02_02_03_01 : b4RowContribution (![2, 4, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 8] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 8 = 21
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 133 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 8^2 = 133
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_01

theorem weighted_02_02_03_01 : b4RawGapContribution ![2, 2, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 1] = b4GapPatternWeight 2 3 1 * 0 :=
      b4GapContribution_from_row 2 2 3 1 0 row_02_02_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_01

theorem row_02_02_03_02 : b4RowContribution (![2, 4, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 9] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 9 = 22
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 150 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 9^2 = 150
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_02

theorem weighted_02_02_03_02 : b4RawGapContribution ![2, 2, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 2] = b4GapPatternWeight 2 3 2 * 0 :=
      b4GapContribution_from_row 2 2 3 2 0 row_02_02_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_02

theorem row_02_02_03_03 : b4RowContribution (![2, 4, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 10] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 10 = 23
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 169 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 10^2 = 169
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_03

theorem weighted_02_02_03_03 : b4RawGapContribution ![2, 2, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 3] = b4GapPatternWeight 2 3 3 * 0 :=
      b4GapContribution_from_row 2 2 3 3 0 row_02_02_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_03

theorem row_02_02_03_04 : b4RowContribution (![2, 4, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 11] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 11 = 24
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 190 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 11^2 = 190
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_04

theorem weighted_02_02_03_04 : b4RawGapContribution ![2, 2, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 4] = b4GapPatternWeight 2 3 4 * 0 :=
      b4GapContribution_from_row 2 2 3 4 0 row_02_02_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_04

def layers_02_02_03_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 14, 15, 15, 14, 12, 9, 6, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 31, 45, 60, 75, 89, 101, 110, 116, 119, 119, 116, 110, 101, 89, 75]]
#print axioms Paper7MomentGapNumeric.layers_02_02_03_05

theorem cells_02_02_03_05 : QTableValid (![2, 4, 7, 12] : Fin 4 → ℕ) layers_02_02_03_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_02_03_05

theorem valid_02_02_03_05 :
    SparseRowValid (![2, 4, 7, 12] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_02_02_03_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 4, 7, 12] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 2 + 4 + 7 + 12 = 25
      decide
    have hzsq : (∑ i, (((![2, 4, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 213 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 4^2 + 7^2 + 12^2 = 213
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_02_03_05
#print axioms Paper7MomentGapNumeric.valid_02_02_03_05

def qvalues_02_02_03_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 119, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_02_03_05

theorem row_02_02_03_05 : b4RowContribution (![2, 4, 7, 12] : Fin 4 → ℕ) = 119 := by
  calc
    b4RowContribution (![2, 4, 7, 12] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_02_02_03_05) :=
      sparseRow_sound (![2, 4, 7, 12] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_02_02_03_05) valid_02_02_03_05
    _ = 119 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_02_03_05 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 119 := by decide
#print axioms Paper7MomentGapNumeric.row_02_02_03_05

theorem weighted_02_02_03_05 : b4RawGapContribution ![2, 2, 3, 5] = 2856 := by
  calc
    b4RawGapContribution ![2, 2, 3, 5] = b4GapPatternWeight 2 3 5 * 119 :=
      b4GapContribution_from_row 2 2 3 5 119 row_02_02_03_05
    _ = 2856 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_05

def layers_02_02_03_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 14, 15, 15, 14, 12, 9, 6, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 31, 45, 60, 75, 89, 101, 110, 116, 119, 120, 119, 116, 110, 101, 89]]
#print axioms Paper7MomentGapNumeric.layers_02_02_03_06

theorem cells_02_02_03_06 : QTableValid (![2, 4, 7, 13] : Fin 4 → ℕ) layers_02_02_03_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_02_03_06

theorem valid_02_02_03_06 :
    SparseRowValid (![2, 4, 7, 13] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_02_03_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 4, 7, 13] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 2 + 4 + 7 + 13 = 26
      decide
    have hzsq : (∑ i, (((![2, 4, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 238 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 4^2 + 7^2 + 13^2 = 238
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_02_03_06
#print axioms Paper7MomentGapNumeric.valid_02_02_03_06

def qvalues_02_02_03_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_02_03_06

theorem row_02_02_03_06 : b4RowContribution (![2, 4, 7, 13] : Fin 4 → ℕ) = 31 := by
  calc
    b4RowContribution (![2, 4, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_02_02_03_06) :=
      sparseRow_sound (![2, 4, 7, 13] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_02_03_06) valid_02_02_03_06
    _ = 31 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_02_03_06 Q := by
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
        _ = 31 := by decide
#print axioms Paper7MomentGapNumeric.row_02_02_03_06

theorem weighted_02_02_03_06 : b4RawGapContribution ![2, 2, 3, 6] = 744 := by
  calc
    b4RawGapContribution ![2, 2, 3, 6] = b4GapPatternWeight 2 3 6 * 31 :=
      b4GapContribution_from_row 2 2 3 6 31 row_02_02_03_06
    _ = 744 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_06

theorem row_02_02_03_07 : b4RowContribution (![2, 4, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 14] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 14 = 27
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 265 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 14^2 = 265
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_07

theorem weighted_02_02_03_07 : b4RawGapContribution ![2, 2, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 7] = b4GapPatternWeight 2 3 7 * 0 :=
      b4GapContribution_from_row 2 2 3 7 0 row_02_02_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_07

theorem row_02_02_03_08 : b4RowContribution (![2, 4, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 15] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 15 = 28
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 294 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 15^2 = 294
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_08

theorem weighted_02_02_03_08 : b4RawGapContribution ![2, 2, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 8] = b4GapPatternWeight 2 3 8 * 0 :=
      b4GapContribution_from_row 2 2 3 8 0 row_02_02_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_08

theorem row_02_02_03_09 : b4RowContribution (![2, 4, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 16 = 29
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 16^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_09

theorem weighted_02_02_03_09 : b4RawGapContribution ![2, 2, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 9] = b4GapPatternWeight 2 3 9 * 0 :=
      b4GapContribution_from_row 2 2 3 9 0 row_02_02_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_09

theorem row_02_02_03_10 : b4RowContribution (![2, 4, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 17 = 30
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 358 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 17^2 = 358
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_10

theorem weighted_02_02_03_10 : b4RawGapContribution ![2, 2, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 10] = b4GapPatternWeight 2 3 10 * 0 :=
      b4GapContribution_from_row 2 2 3 10 0 row_02_02_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_10

theorem row_02_02_03_11 : b4RowContribution (![2, 4, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 18 = 31
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 393 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 18^2 = 393
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_11

theorem weighted_02_02_03_11 : b4RawGapContribution ![2, 2, 3, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 11] = b4GapPatternWeight 2 3 11 * 0 :=
      b4GapContribution_from_row 2 2 3 11 0 row_02_02_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_11

theorem row_02_02_03_12 : b4RowContribution (![2, 4, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 19 = 32
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 430 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 19^2 = 430
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_12

theorem weighted_02_02_03_12 : b4RawGapContribution ![2, 2, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 12] = b4GapPatternWeight 2 3 12 * 0 :=
      b4GapContribution_from_row 2 2 3 12 0 row_02_02_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_12

theorem row_02_02_03_13 : b4RowContribution (![2, 4, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 20 = 33
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 469 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 20^2 = 469
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_13

theorem weighted_02_02_03_13 : b4RawGapContribution ![2, 2, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 13] = b4GapPatternWeight 2 3 13 * 0 :=
      b4GapContribution_from_row 2 2 3 13 0 row_02_02_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_13

theorem row_02_02_03_14 : b4RowContribution (![2, 4, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 21] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 21 = 34
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 510 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 21^2 = 510
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_14

theorem weighted_02_02_03_14 : b4RawGapContribution ![2, 2, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 14] = b4GapPatternWeight 2 3 14 * 0 :=
      b4GapContribution_from_row 2 2 3 14 0 row_02_02_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_14

theorem row_02_02_03_15 : b4RowContribution (![2, 4, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 22 = 35
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 553 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 22^2 = 553
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_15

theorem weighted_02_02_03_15 : b4RawGapContribution ![2, 2, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 15] = b4GapPatternWeight 2 3 15 * 0 :=
      b4GapContribution_from_row 2 2 3 15 0 row_02_02_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_15

theorem row_02_02_03_16 : b4RowContribution (![2, 4, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 23 = 36
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 598 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 23^2 = 598
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_16

theorem weighted_02_02_03_16 : b4RawGapContribution ![2, 2, 3, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 16] = b4GapPatternWeight 2 3 16 * 0 :=
      b4GapContribution_from_row 2 2 3 16 0 row_02_02_03_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_16

theorem row_02_02_03_17 : b4RowContribution (![2, 4, 7, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 7, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 7 + 24 = 37
    decide
  have hzsq : (∑ i, (((![2, 4, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 645 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 7^2 + 24^2 = 645
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_03_17

theorem weighted_02_02_03_17 : b4RawGapContribution ![2, 2, 3, 17] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 3, 17] = b4GapPatternWeight 2 3 17 * 0 :=
      b4GapContribution_from_row 2 2 3 17 0 row_02_02_03_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_03_17

def dvalues_02_02_03 : Fin 18 → ℕ := ![0, 0, 0, 0, 0, 2856, 744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_02_03

theorem dblock_02_02_03 : b4GapPatternDBlock 2 2 3 = 3600 := by
  calc
    b4GapPatternDBlock 2 2 3 = ∑ d : Fin 18, dvalues_02_02_03 d := by
      apply b4GapDBlock_of_rows 2 2 3 dvalues_02_02_03
      intro d
      fin_cases d
      · exact weighted_02_02_03_00
      · exact weighted_02_02_03_01
      · exact weighted_02_02_03_02
      · exact weighted_02_02_03_03
      · exact weighted_02_02_03_04
      · exact weighted_02_02_03_05
      · exact weighted_02_02_03_06
      · exact weighted_02_02_03_07
      · exact weighted_02_02_03_08
      · exact weighted_02_02_03_09
      · exact weighted_02_02_03_10
      · exact weighted_02_02_03_11
      · exact weighted_02_02_03_12
      · exact weighted_02_02_03_13
      · exact weighted_02_02_03_14
      · exact weighted_02_02_03_15
      · exact weighted_02_02_03_16
      · exact weighted_02_02_03_17
    _ = 3600 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_02_03

end Paper7MomentGapNumeric
