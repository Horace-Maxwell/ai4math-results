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

theorem row_03_01_00_00 : b4RowContribution (![3, 4, 4, 4] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 4] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 4 = 15
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 57 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 4^2 = 57
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_00

theorem weighted_03_01_00_00 : b4RawGapContribution ![3, 1, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 0] = b4GapPatternWeight 1 0 0 * 0 :=
      b4GapContribution_from_row 3 1 0 0 0 row_03_01_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_00

theorem row_03_01_00_01 : b4RowContribution (![3, 4, 4, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 5] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 5 = 16
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 66 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 5^2 = 66
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_01

theorem weighted_03_01_00_01 : b4RawGapContribution ![3, 1, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 1] = b4GapPatternWeight 1 0 1 * 0 :=
      b4GapContribution_from_row 3 1 0 1 0 row_03_01_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_01

theorem row_03_01_00_02 : b4RowContribution (![3, 4, 4, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 6] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 6 = 17
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 77 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 6^2 = 77
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_02

theorem weighted_03_01_00_02 : b4RawGapContribution ![3, 1, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 2] = b4GapPatternWeight 1 0 2 * 0 :=
      b4GapContribution_from_row 3 1 0 2 0 row_03_01_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_02

theorem row_03_01_00_03 : b4RowContribution (![3, 4, 4, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 7] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 7 = 18
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 90 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 7^2 = 90
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_03

theorem weighted_03_01_00_03 : b4RawGapContribution ![3, 1, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 3] = b4GapPatternWeight 1 0 3 * 0 :=
      b4GapContribution_from_row 3 1 0 3 0 row_03_01_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_03

theorem row_03_01_00_04 : b4RowContribution (![3, 4, 4, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 8] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 8 = 19
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 105 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 8^2 = 105
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_04

theorem weighted_03_01_00_04 : b4RawGapContribution ![3, 1, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 4] = b4GapPatternWeight 1 0 4 * 0 :=
      b4GapContribution_from_row 3 1 0 4 0 row_03_01_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_04

theorem row_03_01_00_05 : b4RowContribution (![3, 4, 4, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 9] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 9 = 20
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 122 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 9^2 = 122
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_05

theorem weighted_03_01_00_05 : b4RawGapContribution ![3, 1, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 5] = b4GapPatternWeight 1 0 5 * 0 :=
      b4GapContribution_from_row 3 1 0 5 0 row_03_01_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_05

theorem row_03_01_00_06 : b4RowContribution (![3, 4, 4, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 10] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 10 = 21
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 141 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 10^2 = 141
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_06

theorem weighted_03_01_00_06 : b4RawGapContribution ![3, 1, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 6] = b4GapPatternWeight 1 0 6 * 0 :=
      b4GapContribution_from_row 3 1 0 6 0 row_03_01_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_06

theorem row_03_01_00_07 : b4RowContribution (![3, 4, 4, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 11] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 11 = 22
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 162 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 11^2 = 162
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_07

theorem weighted_03_01_00_07 : b4RawGapContribution ![3, 1, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 7] = b4GapPatternWeight 1 0 7 * 0 :=
      b4GapContribution_from_row 3 1 0 7 0 row_03_01_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_07

theorem row_03_01_00_08 : b4RowContribution (![3, 4, 4, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 12] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 12 = 23
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 185 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 12^2 = 185
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_08

theorem weighted_03_01_00_08 : b4RawGapContribution ![3, 1, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 8] = b4GapPatternWeight 1 0 8 * 0 :=
      b4GapContribution_from_row 3 1 0 8 0 row_03_01_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_08

theorem row_03_01_00_09 : b4RowContribution (![3, 4, 4, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 13] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 13 = 24
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 210 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 13^2 = 210
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_09

theorem weighted_03_01_00_09 : b4RawGapContribution ![3, 1, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 9] = b4GapPatternWeight 1 0 9 * 0 :=
      b4GapContribution_from_row 3 1 0 9 0 row_03_01_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_09

def layers_03_01_00_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 16, 16, 14, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 34, 50, 66, 80, 90, 96, 99, 100, 100, 100, 100, 99, 96, 90, 80]]
#print axioms Paper7MomentGapNumeric.layers_03_01_00_10

theorem cells_03_01_00_10 : QTableValid (![3, 4, 4, 14] : Fin 4 → ℕ) layers_03_01_00_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_01_00_10

theorem valid_03_01_00_10 :
    SparseRowValid (![3, 4, 4, 14] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_03_01_00_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 4, 4, 14] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 3 + 4 + 4 + 14 = 25
      decide
    have hzsq : (∑ i, (((![3, 4, 4, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 237 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 4^2 + 4^2 + 14^2 = 237
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_01_00_10
#print axioms Paper7MomentGapNumeric.valid_03_01_00_10

def qvalues_03_01_00_10 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_01_00_10

theorem row_03_01_00_10 : b4RowContribution (![3, 4, 4, 14] : Fin 4 → ℕ) = 67 := by
  calc
    b4RowContribution (![3, 4, 4, 14] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_03_01_00_10) :=
      sparseRow_sound (![3, 4, 4, 14] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_03_01_00_10) valid_03_01_00_10
    _ = 67 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_01_00_10 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 67 := by decide
#print axioms Paper7MomentGapNumeric.row_03_01_00_10

theorem weighted_03_01_00_10 : b4RawGapContribution ![3, 1, 0, 10] = 804 := by
  calc
    b4RawGapContribution ![3, 1, 0, 10] = b4GapPatternWeight 1 0 10 * 67 :=
      b4GapContribution_from_row 3 1 0 10 67 row_03_01_00_10
    _ = 804 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_10

theorem row_03_01_00_11 : b4RowContribution (![3, 4, 4, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 15] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 15 = 26
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 266 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 15^2 = 266
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_11

theorem weighted_03_01_00_11 : b4RawGapContribution ![3, 1, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 11] = b4GapPatternWeight 1 0 11 * 0 :=
      b4GapContribution_from_row 3 1 0 11 0 row_03_01_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_11

theorem row_03_01_00_12 : b4RowContribution (![3, 4, 4, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 16] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 16 = 27
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 297 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 16^2 = 297
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_12

theorem weighted_03_01_00_12 : b4RawGapContribution ![3, 1, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 12] = b4GapPatternWeight 1 0 12 * 0 :=
      b4GapContribution_from_row 3 1 0 12 0 row_03_01_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_12

theorem row_03_01_00_13 : b4RowContribution (![3, 4, 4, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 17] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 17 = 28
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 330 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 17^2 = 330
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_13

theorem weighted_03_01_00_13 : b4RawGapContribution ![3, 1, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 13] = b4GapPatternWeight 1 0 13 * 0 :=
      b4GapContribution_from_row 3 1 0 13 0 row_03_01_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_13

theorem row_03_01_00_14 : b4RowContribution (![3, 4, 4, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 18] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 18 = 29
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 365 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 18^2 = 365
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_14

theorem weighted_03_01_00_14 : b4RawGapContribution ![3, 1, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 14] = b4GapPatternWeight 1 0 14 * 0 :=
      b4GapContribution_from_row 3 1 0 14 0 row_03_01_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_14

theorem row_03_01_00_15 : b4RowContribution (![3, 4, 4, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 19] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 19 = 30
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 402 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 19^2 = 402
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_15

theorem weighted_03_01_00_15 : b4RawGapContribution ![3, 1, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 15] = b4GapPatternWeight 1 0 15 * 0 :=
      b4GapContribution_from_row 3 1 0 15 0 row_03_01_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_15

theorem row_03_01_00_16 : b4RowContribution (![3, 4, 4, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 20] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 20 = 31
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 441 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 20^2 = 441
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_16

theorem weighted_03_01_00_16 : b4RawGapContribution ![3, 1, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 16] = b4GapPatternWeight 1 0 16 * 0 :=
      b4GapContribution_from_row 3 1 0 16 0 row_03_01_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_16

theorem row_03_01_00_17 : b4RowContribution (![3, 4, 4, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 21] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 21 = 32
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 482 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 21^2 = 482
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_17

theorem weighted_03_01_00_17 : b4RawGapContribution ![3, 1, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 17] = b4GapPatternWeight 1 0 17 * 0 :=
      b4GapContribution_from_row 3 1 0 17 0 row_03_01_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_17

theorem row_03_01_00_18 : b4RowContribution (![3, 4, 4, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 22] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 22 = 33
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 525 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 22^2 = 525
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_18

theorem weighted_03_01_00_18 : b4RawGapContribution ![3, 1, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 18] = b4GapPatternWeight 1 0 18 * 0 :=
      b4GapContribution_from_row 3 1 0 18 0 row_03_01_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_18

def layers_03_01_00_19 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 16, 16, 14, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 34, 50, 66, 80, 90, 96, 99, 100, 100, 100, 100, 100, 100, 100, 100]]
#print axioms Paper7MomentGapNumeric.layers_03_01_00_19

theorem cells_03_01_00_19 : QTableValid (![3, 4, 4, 23] : Fin 4 → ℕ) layers_03_01_00_19 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_01_00_19

theorem valid_03_01_00_19 :
    SparseRowValid (![3, 4, 4, 23] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_03_01_00_19) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 4, 4, 23] : Fin 4 → ℕ) i) = 34 := by
      rw [Fin.sum_univ_four]
      change 3 + 4 + 4 + 23 = 34
      decide
    have hzsq : (∑ i, (((![3, 4, 4, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 570 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 4^2 + 4^2 + 23^2 = 570
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_01_00_19
#print axioms Paper7MomentGapNumeric.valid_03_01_00_19

def qvalues_03_01_00_19 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_01_00_19

theorem row_03_01_00_19 : b4RowContribution (![3, 4, 4, 23] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![3, 4, 4, 23] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_03_01_00_19) :=
      sparseRow_sound (![3, 4, 4, 23] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_03_01_00_19) valid_03_01_00_19
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_01_00_19 Q := by
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
#print axioms Paper7MomentGapNumeric.row_03_01_00_19

theorem weighted_03_01_00_19 : b4RawGapContribution ![3, 1, 0, 19] = 12 := by
  calc
    b4RawGapContribution ![3, 1, 0, 19] = b4GapPatternWeight 1 0 19 * 1 :=
      b4GapContribution_from_row 3 1 0 19 1 row_03_01_00_19
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_19

theorem row_03_01_00_20 : b4RowContribution (![3, 4, 4, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 24] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 24 = 35
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 617 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 24^2 = 617
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_20

theorem weighted_03_01_00_20 : b4RawGapContribution ![3, 1, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 20] = b4GapPatternWeight 1 0 20 * 0 :=
      b4GapContribution_from_row 3 1 0 20 0 row_03_01_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_20

theorem row_03_01_00_21 : b4RowContribution (![3, 4, 4, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 4, 25] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 4 + 25 = 36
    decide
  have hzsq : (∑ i, (((![3, 4, 4, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 666 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 4^2 + 25^2 = 666
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_00_21

theorem weighted_03_01_00_21 : b4RawGapContribution ![3, 1, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 0, 21] = b4GapPatternWeight 1 0 21 * 0 :=
      b4GapContribution_from_row 3 1 0 21 0 row_03_01_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_21

def layers_03_01_00_22 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 16, 16, 14, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 34, 50, 66, 80, 90, 96, 99, 100, 100, 100, 100, 100, 100, 100, 100]]
#print axioms Paper7MomentGapNumeric.layers_03_01_00_22

theorem cells_03_01_00_22 : QTableValid (![3, 4, 4, 26] : Fin 4 → ℕ) layers_03_01_00_22 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_01_00_22

theorem valid_03_01_00_22 :
    SparseRowValid (![3, 4, 4, 26] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_03_01_00_22) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 4, 4, 26] : Fin 4 → ℕ) i) = 37 := by
      rw [Fin.sum_univ_four]
      change 3 + 4 + 4 + 26 = 37
      decide
    have hzsq : (∑ i, (((![3, 4, 4, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 717 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 4^2 + 4^2 + 26^2 = 717
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_01_00_22
#print axioms Paper7MomentGapNumeric.valid_03_01_00_22

def qvalues_03_01_00_22 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_01_00_22

theorem row_03_01_00_22 : b4RowContribution (![3, 4, 4, 26] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![3, 4, 4, 26] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_03_01_00_22) :=
      sparseRow_sound (![3, 4, 4, 26] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_03_01_00_22) valid_03_01_00_22
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_01_00_22 Q := by
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
#print axioms Paper7MomentGapNumeric.row_03_01_00_22

theorem weighted_03_01_00_22 : b4RawGapContribution ![3, 1, 0, 22] = 12 := by
  calc
    b4RawGapContribution ![3, 1, 0, 22] = b4GapPatternWeight 1 0 22 * 1 :=
      b4GapContribution_from_row 3 1 0 22 1 row_03_01_00_22
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_00_22

def dvalues_03_01_00 : Fin 23 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 804, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 12]
#print axioms Paper7MomentGapNumeric.dvalues_03_01_00

theorem dblock_03_01_00 : b4GapPatternDBlock 3 1 0 = 828 := by
  calc
    b4GapPatternDBlock 3 1 0 = ∑ d : Fin 23, dvalues_03_01_00 d := by
      apply b4GapDBlock_of_rows 3 1 0 dvalues_03_01_00
      intro d
      fin_cases d
      · exact weighted_03_01_00_00
      · exact weighted_03_01_00_01
      · exact weighted_03_01_00_02
      · exact weighted_03_01_00_03
      · exact weighted_03_01_00_04
      · exact weighted_03_01_00_05
      · exact weighted_03_01_00_06
      · exact weighted_03_01_00_07
      · exact weighted_03_01_00_08
      · exact weighted_03_01_00_09
      · exact weighted_03_01_00_10
      · exact weighted_03_01_00_11
      · exact weighted_03_01_00_12
      · exact weighted_03_01_00_13
      · exact weighted_03_01_00_14
      · exact weighted_03_01_00_15
      · exact weighted_03_01_00_16
      · exact weighted_03_01_00_17
      · exact weighted_03_01_00_18
      · exact weighted_03_01_00_19
      · exact weighted_03_01_00_20
      · exact weighted_03_01_00_21
      · exact weighted_03_01_00_22
    _ = 828 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_01_00

end Paper7MomentGapNumeric
