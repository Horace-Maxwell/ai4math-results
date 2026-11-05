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

theorem row_02_00_04_00 : b4RowContribution (![2, 2, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 6] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 6 = 16
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 80 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 6^2 = 80
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_00

theorem weighted_02_00_04_00 : b4RawGapContribution ![2, 0, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 0] = b4GapPatternWeight 0 4 0 * 0 :=
      b4GapContribution_from_row 2 0 4 0 0 row_02_00_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_00

theorem row_02_00_04_01 : b4RowContribution (![2, 2, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 7] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 7 = 17
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 93 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 7^2 = 93
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_01

theorem weighted_02_00_04_01 : b4RawGapContribution ![2, 0, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 1] = b4GapPatternWeight 0 4 1 * 0 :=
      b4GapContribution_from_row 2 0 4 1 0 row_02_00_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_01

theorem row_02_00_04_02 : b4RowContribution (![2, 2, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 8] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 8 = 18
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 108 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 8^2 = 108
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_02

theorem weighted_02_00_04_02 : b4RawGapContribution ![2, 0, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 2] = b4GapPatternWeight 0 4 2 * 0 :=
      b4GapContribution_from_row 2 0 4 2 0 row_02_00_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_02

theorem row_02_00_04_03 : b4RowContribution (![2, 2, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 9] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 9 = 19
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 125 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 9^2 = 125
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_03

theorem weighted_02_00_04_03 : b4RawGapContribution ![2, 0, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 3] = b4GapPatternWeight 0 4 3 * 0 :=
      b4GapContribution_from_row 2 0 4 3 0 row_02_00_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_03

theorem row_02_00_04_04 : b4RowContribution (![2, 2, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 10] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 10 = 20
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 144 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 10^2 = 144
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_04

theorem weighted_02_00_04_04 : b4RawGapContribution ![2, 0, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 4] = b4GapPatternWeight 0 4 4 * 0 :=
      b4GapContribution_from_row 2 0 4 4 0 row_02_00_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_04

theorem row_02_00_04_05 : b4RowContribution (![2, 2, 6, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 11] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 11 = 21
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 165 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 11^2 = 165
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_05

theorem weighted_02_00_04_05 : b4RawGapContribution ![2, 0, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 5] = b4GapPatternWeight 0 4 5 * 0 :=
      b4GapContribution_from_row 2 0 4 5 0 row_02_00_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_05

theorem row_02_00_04_06 : b4RowContribution (![2, 2, 6, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 12] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 12 = 22
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 188 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 12^2 = 188
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_06

theorem weighted_02_00_04_06 : b4RawGapContribution ![2, 0, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 6] = b4GapPatternWeight 0 4 6 * 0 :=
      b4GapContribution_from_row 2 0 4 6 0 row_02_00_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_06

theorem row_02_00_04_07 : b4RowContribution (![2, 2, 6, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 13] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 13 = 23
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 213 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 13^2 = 213
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_07

theorem weighted_02_00_04_07 : b4RawGapContribution ![2, 0, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 7] = b4GapPatternWeight 0 4 7 * 0 :=
      b4GapContribution_from_row 2 0 4 7 0 row_02_00_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_07

def layers_02_00_04_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 36, 45, 53, 59, 62, 63, 63, 63, 63, 63, 62, 59, 53, 45]]
#print axioms Paper7MomentGapNumeric.layers_02_00_04_08

theorem cells_02_00_04_08 : QTableValid (![2, 2, 6, 14] : Fin 4 → ℕ) layers_02_00_04_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_04_08

theorem valid_02_00_04_08 :
    SparseRowValid (![2, 2, 6, 14] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_02_00_04_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 6, 14] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 6 + 14 = 24
      decide
    have hzsq : (∑ i, (((![2, 2, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 240 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 6^2 + 14^2 = 240
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_04_08
#print axioms Paper7MomentGapNumeric.valid_02_00_04_08

def qvalues_02_00_04_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_04_08

theorem row_02_00_04_08 : b4RowContribution (![2, 2, 6, 14] : Fin 4 → ℕ) = 45 := by
  calc
    b4RowContribution (![2, 2, 6, 14] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_02_00_04_08) :=
      sparseRow_sound (![2, 2, 6, 14] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_02_00_04_08) valid_02_00_04_08
    _ = 45 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_04_08 Q := by
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
        _ = 45 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_04_08

theorem weighted_02_00_04_08 : b4RawGapContribution ![2, 0, 4, 8] = 540 := by
  calc
    b4RawGapContribution ![2, 0, 4, 8] = b4GapPatternWeight 0 4 8 * 45 :=
      b4GapContribution_from_row 2 0 4 8 45 row_02_00_04_08
    _ = 540 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_08

theorem row_02_00_04_09 : b4RowContribution (![2, 2, 6, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 15] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 15 = 25
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 269 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 15^2 = 269
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_09

theorem weighted_02_00_04_09 : b4RawGapContribution ![2, 0, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 9] = b4GapPatternWeight 0 4 9 * 0 :=
      b4GapContribution_from_row 2 0 4 9 0 row_02_00_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_09

theorem row_02_00_04_10 : b4RowContribution (![2, 2, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 16] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 16 = 26
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 300 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 16^2 = 300
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_10

theorem weighted_02_00_04_10 : b4RawGapContribution ![2, 0, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 10] = b4GapPatternWeight 0 4 10 * 0 :=
      b4GapContribution_from_row 2 0 4 10 0 row_02_00_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_10

theorem row_02_00_04_11 : b4RowContribution (![2, 2, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 17] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 17 = 27
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 333 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 17^2 = 333
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_11

theorem weighted_02_00_04_11 : b4RawGapContribution ![2, 0, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 11] = b4GapPatternWeight 0 4 11 * 0 :=
      b4GapContribution_from_row 2 0 4 11 0 row_02_00_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_11

theorem row_02_00_04_12 : b4RowContribution (![2, 2, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 18] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 18 = 28
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 368 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 18^2 = 368
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_12

theorem weighted_02_00_04_12 : b4RawGapContribution ![2, 0, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 12] = b4GapPatternWeight 0 4 12 * 0 :=
      b4GapContribution_from_row 2 0 4 12 0 row_02_00_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_12

theorem row_02_00_04_13 : b4RowContribution (![2, 2, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 19] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 19 = 29
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 405 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 19^2 = 405
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_13

theorem weighted_02_00_04_13 : b4RawGapContribution ![2, 0, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 13] = b4GapPatternWeight 0 4 13 * 0 :=
      b4GapContribution_from_row 2 0 4 13 0 row_02_00_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_13

theorem row_02_00_04_14 : b4RowContribution (![2, 2, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 20] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 20 = 30
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 444 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 20^2 = 444
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_14

theorem weighted_02_00_04_14 : b4RawGapContribution ![2, 0, 4, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 14] = b4GapPatternWeight 0 4 14 * 0 :=
      b4GapContribution_from_row 2 0 4 14 0 row_02_00_04_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_14

theorem row_02_00_04_15 : b4RowContribution (![2, 2, 6, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 21] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 21 = 31
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 485 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 21^2 = 485
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_15

theorem weighted_02_00_04_15 : b4RawGapContribution ![2, 0, 4, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 15] = b4GapPatternWeight 0 4 15 * 0 :=
      b4GapContribution_from_row 2 0 4 15 0 row_02_00_04_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_15

theorem row_02_00_04_16 : b4RowContribution (![2, 2, 6, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 22] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 22 = 32
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 528 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 22^2 = 528
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_16

theorem weighted_02_00_04_16 : b4RawGapContribution ![2, 0, 4, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 16] = b4GapPatternWeight 0 4 16 * 0 :=
      b4GapContribution_from_row 2 0 4 16 0 row_02_00_04_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_16

theorem row_02_00_04_17 : b4RowContribution (![2, 2, 6, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 23] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 23 = 33
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 573 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 23^2 = 573
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_17

theorem weighted_02_00_04_17 : b4RawGapContribution ![2, 0, 4, 17] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 17] = b4GapPatternWeight 0 4 17 * 0 :=
      b4GapContribution_from_row 2 0 4 17 0 row_02_00_04_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_17

theorem row_02_00_04_18 : b4RowContribution (![2, 2, 6, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 24] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 24 = 34
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 620 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 24^2 = 620
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_18

theorem weighted_02_00_04_18 : b4RawGapContribution ![2, 0, 4, 18] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 18] = b4GapPatternWeight 0 4 18 * 0 :=
      b4GapContribution_from_row 2 0 4 18 0 row_02_00_04_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_18

theorem row_02_00_04_19 : b4RowContribution (![2, 2, 6, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 25] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 25 = 35
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 669 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 25^2 = 669
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_19

theorem weighted_02_00_04_19 : b4RawGapContribution ![2, 0, 4, 19] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 19] = b4GapPatternWeight 0 4 19 * 0 :=
      b4GapContribution_from_row 2 0 4 19 0 row_02_00_04_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_19

theorem row_02_00_04_20 : b4RowContribution (![2, 2, 6, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 26] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 26 = 36
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 720 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 26^2 = 720
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_20

theorem weighted_02_00_04_20 : b4RawGapContribution ![2, 0, 4, 20] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 20] = b4GapPatternWeight 0 4 20 * 0 :=
      b4GapContribution_from_row 2 0 4 20 0 row_02_00_04_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_20

theorem row_02_00_04_21 : b4RowContribution (![2, 2, 6, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 6, 27] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 6 + 27 = 37
    decide
  have hzsq : (∑ i, (((![2, 2, 6, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 773 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 6^2 + 27^2 = 773
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_04_21

theorem weighted_02_00_04_21 : b4RawGapContribution ![2, 0, 4, 21] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 4, 21] = b4GapPatternWeight 0 4 21 * 0 :=
      b4GapContribution_from_row 2 0 4 21 0 row_02_00_04_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_04_21

def dvalues_02_00_04 : Fin 22 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 540, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_00_04

theorem dblock_02_00_04 : b4GapPatternDBlock 2 0 4 = 540 := by
  calc
    b4GapPatternDBlock 2 0 4 = ∑ d : Fin 22, dvalues_02_00_04 d := by
      apply b4GapDBlock_of_rows 2 0 4 dvalues_02_00_04
      intro d
      fin_cases d
      · exact weighted_02_00_04_00
      · exact weighted_02_00_04_01
      · exact weighted_02_00_04_02
      · exact weighted_02_00_04_03
      · exact weighted_02_00_04_04
      · exact weighted_02_00_04_05
      · exact weighted_02_00_04_06
      · exact weighted_02_00_04_07
      · exact weighted_02_00_04_08
      · exact weighted_02_00_04_09
      · exact weighted_02_00_04_10
      · exact weighted_02_00_04_11
      · exact weighted_02_00_04_12
      · exact weighted_02_00_04_13
      · exact weighted_02_00_04_14
      · exact weighted_02_00_04_15
      · exact weighted_02_00_04_16
      · exact weighted_02_00_04_17
      · exact weighted_02_00_04_18
      · exact weighted_02_00_04_19
      · exact weighted_02_00_04_20
      · exact weighted_02_00_04_21
    _ = 540 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_00_04

end Paper7MomentGapNumeric
