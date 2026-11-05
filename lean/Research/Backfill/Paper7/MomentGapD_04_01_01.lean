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

theorem row_04_01_01_00 : b4RowContribution (![4, 5, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 6] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 6 = 21
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 113 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 6^2 = 113
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_00

theorem weighted_04_01_01_00 : b4RawGapContribution ![4, 1, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 0] = b4GapPatternWeight 1 1 0 * 0 :=
      b4GapContribution_from_row 4 1 1 0 0 row_04_01_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_00

theorem row_04_01_01_01 : b4RowContribution (![4, 5, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 7] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 7 = 22
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 126 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 7^2 = 126
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_01

theorem weighted_04_01_01_01 : b4RawGapContribution ![4, 1, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 1] = b4GapPatternWeight 1 1 1 * 0 :=
      b4GapContribution_from_row 4 1 1 1 0 row_04_01_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_01

theorem row_04_01_01_02 : b4RowContribution (![4, 5, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 8] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 8 = 23
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 141 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 8^2 = 141
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_02

theorem weighted_04_01_01_02 : b4RawGapContribution ![4, 1, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 2] = b4GapPatternWeight 1 1 2 * 0 :=
      b4GapContribution_from_row 4 1 1 2 0 row_04_01_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_02

theorem row_04_01_01_03 : b4RowContribution (![4, 5, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 9] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 9 = 24
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 158 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 9^2 = 158
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_03

theorem weighted_04_01_01_03 : b4RawGapContribution ![4, 1, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 3] = b4GapPatternWeight 1 1 3 * 0 :=
      b4GapContribution_from_row 4 1 1 3 0 row_04_01_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_03

theorem row_04_01_01_04 : b4RowContribution (![4, 5, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 10] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 10 = 25
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 177 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 10^2 = 177
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_04

theorem weighted_04_01_01_04 : b4RawGapContribution ![4, 1, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 4] = b4GapPatternWeight 1 1 4 * 0 :=
      b4GapContribution_from_row 4 1 1 4 0 row_04_01_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_04

theorem row_04_01_01_05 : b4RowContribution (![4, 5, 6, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 11] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 11 = 26
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 198 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 11^2 = 198
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_05

theorem weighted_04_01_01_05 : b4RawGapContribution ![4, 1, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 5] = b4GapPatternWeight 1 1 5 * 0 :=
      b4GapContribution_from_row 4 1 1 5 0 row_04_01_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_05

theorem row_04_01_01_06 : b4RowContribution (![4, 5, 6, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 12] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 12 = 27
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 221 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 12^2 = 221
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_06

theorem weighted_04_01_01_06 : b4RawGapContribution ![4, 1, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 6] = b4GapPatternWeight 1 1 6 * 0 :=
      b4GapContribution_from_row 4 1 1 6 0 row_04_01_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_06

theorem row_04_01_01_07 : b4RowContribution (![4, 5, 6, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 13 = 28
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 246 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 13^2 = 246
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_07

theorem weighted_04_01_01_07 : b4RawGapContribution ![4, 1, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 7] = b4GapPatternWeight 1 1 7 * 0 :=
      b4GapContribution_from_row 4 1 1 7 0 row_04_01_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_07

def layers_04_01_01_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 24, 26, 26, 24, 20, 15, 10, 6, 3, 1, 0, 0, 0], ![1, 4, 10, 20, 35, 55, 79, 105, 131, 155, 175, 190, 200, 206, 209, 209, 206, 200, 190]]
#print axioms Paper7MomentGapNumeric.layers_04_01_01_08

theorem cells_04_01_01_08 : QTableValid (![4, 5, 6, 14] : Fin 4 → ℕ) layers_04_01_01_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_01_01_08

theorem valid_04_01_01_08 :
    SparseRowValid (![4, 5, 6, 14] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_04_01_01_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 5, 6, 14] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 4 + 5 + 6 + 14 = 29
      decide
    have hzsq : (∑ i, (((![4, 5, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 273 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 5^2 + 6^2 + 14^2 = 273
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_01_01_08
#print axioms Paper7MomentGapNumeric.valid_04_01_01_08

def qvalues_04_01_01_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 79, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_01_01_08

theorem row_04_01_01_08 : b4RowContribution (![4, 5, 6, 14] : Fin 4 → ℕ) = 79 := by
  calc
    b4RowContribution (![4, 5, 6, 14] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_04_01_01_08) :=
      sparseRow_sound (![4, 5, 6, 14] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_04_01_01_08) valid_04_01_01_08
    _ = 79 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_01_01_08 Q := by
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
        _ = 79 := by decide
#print axioms Paper7MomentGapNumeric.row_04_01_01_08

theorem weighted_04_01_01_08 : b4RawGapContribution ![4, 1, 1, 8] = 1896 := by
  calc
    b4RawGapContribution ![4, 1, 1, 8] = b4GapPatternWeight 1 1 8 * 79 :=
      b4GapContribution_from_row 4 1 1 8 79 row_04_01_01_08
    _ = 1896 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_08

theorem row_04_01_01_09 : b4RowContribution (![4, 5, 6, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 15 = 30
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 302 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 15^2 = 302
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_09

theorem weighted_04_01_01_09 : b4RawGapContribution ![4, 1, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 9] = b4GapPatternWeight 1 1 9 * 0 :=
      b4GapContribution_from_row 4 1 1 9 0 row_04_01_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_09

theorem row_04_01_01_10 : b4RowContribution (![4, 5, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 16 = 31
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 333 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 16^2 = 333
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_10

theorem weighted_04_01_01_10 : b4RawGapContribution ![4, 1, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 10] = b4GapPatternWeight 1 1 10 * 0 :=
      b4GapContribution_from_row 4 1 1 10 0 row_04_01_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_10

theorem row_04_01_01_11 : b4RowContribution (![4, 5, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 17 = 32
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 366 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 17^2 = 366
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_11

theorem weighted_04_01_01_11 : b4RawGapContribution ![4, 1, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 11] = b4GapPatternWeight 1 1 11 * 0 :=
      b4GapContribution_from_row 4 1 1 11 0 row_04_01_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_11

theorem row_04_01_01_12 : b4RowContribution (![4, 5, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 18 = 33
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 401 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 18^2 = 401
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_12

theorem weighted_04_01_01_12 : b4RawGapContribution ![4, 1, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 12] = b4GapPatternWeight 1 1 12 * 0 :=
      b4GapContribution_from_row 4 1 1 12 0 row_04_01_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_12

theorem row_04_01_01_13 : b4RowContribution (![4, 5, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 19 = 34
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 438 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 19^2 = 438
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_13

theorem weighted_04_01_01_13 : b4RawGapContribution ![4, 1, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 13] = b4GapPatternWeight 1 1 13 * 0 :=
      b4GapContribution_from_row 4 1 1 13 0 row_04_01_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_13

theorem row_04_01_01_14 : b4RowContribution (![4, 5, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 20 = 35
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 477 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 20^2 = 477
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_14

theorem weighted_04_01_01_14 : b4RawGapContribution ![4, 1, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 14] = b4GapPatternWeight 1 1 14 * 0 :=
      b4GapContribution_from_row 4 1 1 14 0 row_04_01_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_14

theorem row_04_01_01_15 : b4RowContribution (![4, 5, 6, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 21 = 36
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 518 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 21^2 = 518
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_15

theorem weighted_04_01_01_15 : b4RawGapContribution ![4, 1, 1, 15] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 15] = b4GapPatternWeight 1 1 15 * 0 :=
      b4GapContribution_from_row 4 1 1 15 0 row_04_01_01_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_15

theorem row_04_01_01_16 : b4RowContribution (![4, 5, 6, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 6, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 6 + 22 = 37
    decide
  have hzsq : (∑ i, (((![4, 5, 6, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 561 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 6^2 + 22^2 = 561
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_01_16

theorem weighted_04_01_01_16 : b4RawGapContribution ![4, 1, 1, 16] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 1, 16] = b4GapPatternWeight 1 1 16 * 0 :=
      b4GapContribution_from_row 4 1 1 16 0 row_04_01_01_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_01_16

def dvalues_04_01_01 : Fin 17 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 1896, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_01_01

theorem dblock_04_01_01 : b4GapPatternDBlock 4 1 1 = 1896 := by
  calc
    b4GapPatternDBlock 4 1 1 = ∑ d : Fin 17, dvalues_04_01_01 d := by
      apply b4GapDBlock_of_rows 4 1 1 dvalues_04_01_01
      intro d
      fin_cases d
      · exact weighted_04_01_01_00
      · exact weighted_04_01_01_01
      · exact weighted_04_01_01_02
      · exact weighted_04_01_01_03
      · exact weighted_04_01_01_04
      · exact weighted_04_01_01_05
      · exact weighted_04_01_01_06
      · exact weighted_04_01_01_07
      · exact weighted_04_01_01_08
      · exact weighted_04_01_01_09
      · exact weighted_04_01_01_10
      · exact weighted_04_01_01_11
      · exact weighted_04_01_01_12
      · exact weighted_04_01_01_13
      · exact weighted_04_01_01_14
      · exact weighted_04_01_01_15
      · exact weighted_04_01_01_16
    _ = 1896 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_01_01

end Paper7MomentGapNumeric
