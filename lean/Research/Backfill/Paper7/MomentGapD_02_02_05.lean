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

theorem row_02_02_05_00 : b4RowContribution (![2, 4, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 9, 9] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 9 + 9 = 24
    decide
  have hzsq : (∑ i, (((![2, 4, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 182 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 9^2 + 9^2 = 182
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_05_00

theorem weighted_02_02_05_00 : b4RawGapContribution ![2, 2, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 5, 0] = b4GapPatternWeight 2 5 0 * 0 :=
      b4GapContribution_from_row 2 2 5 0 0 row_02_02_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_05_00

theorem row_02_02_05_01 : b4RowContribution (![2, 4, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 9, 10] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 9 + 10 = 25
    decide
  have hzsq : (∑ i, (((![2, 4, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 201 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 9^2 + 10^2 = 201
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_05_01

theorem weighted_02_02_05_01 : b4RawGapContribution ![2, 2, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 5, 1] = b4GapPatternWeight 2 5 1 * 0 :=
      b4GapContribution_from_row 2 2 5 1 0 row_02_02_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_05_01

theorem row_02_02_05_02 : b4RowContribution (![2, 4, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 9, 11] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 9 + 11 = 26
    decide
  have hzsq : (∑ i, (((![2, 4, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 222 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 9^2 + 11^2 = 222
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_05_02

theorem weighted_02_02_05_02 : b4RawGapContribution ![2, 2, 5, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 5, 2] = b4GapPatternWeight 2 5 2 * 0 :=
      b4GapContribution_from_row 2 2 5 2 0 row_02_02_05_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_05_02

theorem row_02_02_05_03 : b4RowContribution (![2, 4, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 9, 12] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 9 + 12 = 27
    decide
  have hzsq : (∑ i, (((![2, 4, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 245 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 9^2 + 12^2 = 245
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_05_03

theorem weighted_02_02_05_03 : b4RawGapContribution ![2, 2, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 5, 3] = b4GapPatternWeight 2 5 3 * 0 :=
      b4GapContribution_from_row 2 2 5 3 0 row_02_02_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_05_03

def layers_02_02_05_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 14, 15, 15, 15, 15, 14, 12, 9, 6, 3, 1, 0, 0, 0], ![1, 4, 10, 19, 31, 45, 60, 75, 90, 105, 119, 131, 140, 146, 148, 146, 140, 131, 119]]
#print axioms Paper7MomentGapNumeric.layers_02_02_05_04

theorem cells_02_02_05_04 : QTableValid (![2, 4, 9, 13] : Fin 4 → ℕ) layers_02_02_05_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_02_05_04

theorem valid_02_02_05_04 :
    SparseRowValid (![2, 4, 9, 13] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_02_02_05_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 4, 9, 13] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 2 + 4 + 9 + 13 = 28
      decide
    have hzsq : (∑ i, (((![2, 4, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 4^2 + 9^2 + 13^2 = 270
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_02_05_04
#print axioms Paper7MomentGapNumeric.valid_02_02_05_04

def qvalues_02_02_05_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_02_05_04

theorem row_02_02_05_04 : b4RowContribution (![2, 4, 9, 13] : Fin 4 → ℕ) = 105 := by
  calc
    b4RowContribution (![2, 4, 9, 13] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_02_02_05_04) :=
      sparseRow_sound (![2, 4, 9, 13] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_02_02_05_04) valid_02_02_05_04
    _ = 105 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_02_05_04 Q := by
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
        _ = 105 := by decide
#print axioms Paper7MomentGapNumeric.row_02_02_05_04

theorem weighted_02_02_05_04 : b4RawGapContribution ![2, 2, 5, 4] = 2520 := by
  calc
    b4RawGapContribution ![2, 2, 5, 4] = b4GapPatternWeight 2 5 4 * 105 :=
      b4GapContribution_from_row 2 2 5 4 105 row_02_02_05_04
    _ = 2520 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_05_04

theorem row_02_02_05_05 : b4RowContribution (![2, 4, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 9, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 9 + 14 = 29
    decide
  have hzsq : (∑ i, (((![2, 4, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 297 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 9^2 + 14^2 = 297
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_05_05

theorem weighted_02_02_05_05 : b4RawGapContribution ![2, 2, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 5, 5] = b4GapPatternWeight 2 5 5 * 0 :=
      b4GapContribution_from_row 2 2 5 5 0 row_02_02_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_05_05

theorem row_02_02_05_06 : b4RowContribution (![2, 4, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 9, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 9 + 15 = 30
    decide
  have hzsq : (∑ i, (((![2, 4, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 326 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 9^2 + 15^2 = 326
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_05_06

theorem weighted_02_02_05_06 : b4RawGapContribution ![2, 2, 5, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 5, 6] = b4GapPatternWeight 2 5 6 * 0 :=
      b4GapContribution_from_row 2 2 5 6 0 row_02_02_05_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_05_06

theorem row_02_02_05_07 : b4RowContribution (![2, 4, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 9, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 9 + 16 = 31
    decide
  have hzsq : (∑ i, (((![2, 4, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 357 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 9^2 + 16^2 = 357
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_05_07

theorem weighted_02_02_05_07 : b4RawGapContribution ![2, 2, 5, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 5, 7] = b4GapPatternWeight 2 5 7 * 0 :=
      b4GapContribution_from_row 2 2 5 7 0 row_02_02_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_05_07

theorem row_02_02_05_08 : b4RowContribution (![2, 4, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 9, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 9 + 17 = 32
    decide
  have hzsq : (∑ i, (((![2, 4, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 9^2 + 17^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_05_08

theorem weighted_02_02_05_08 : b4RawGapContribution ![2, 2, 5, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 5, 8] = b4GapPatternWeight 2 5 8 * 0 :=
      b4GapContribution_from_row 2 2 5 8 0 row_02_02_05_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_05_08

theorem row_02_02_05_09 : b4RowContribution (![2, 4, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 9, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 9 + 18 = 33
    decide
  have hzsq : (∑ i, (((![2, 4, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 425 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 9^2 + 18^2 = 425
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_05_09

theorem weighted_02_02_05_09 : b4RawGapContribution ![2, 2, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 5, 9] = b4GapPatternWeight 2 5 9 * 0 :=
      b4GapContribution_from_row 2 2 5 9 0 row_02_02_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_05_09

theorem row_02_02_05_10 : b4RowContribution (![2, 4, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 9, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 9 + 19 = 34
    decide
  have hzsq : (∑ i, (((![2, 4, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 462 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 9^2 + 19^2 = 462
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_05_10

theorem weighted_02_02_05_10 : b4RawGapContribution ![2, 2, 5, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 5, 10] = b4GapPatternWeight 2 5 10 * 0 :=
      b4GapContribution_from_row 2 2 5 10 0 row_02_02_05_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_05_10

theorem row_02_02_05_11 : b4RowContribution (![2, 4, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 9, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 9 + 20 = 35
    decide
  have hzsq : (∑ i, (((![2, 4, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 501 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 9^2 + 20^2 = 501
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_05_11

theorem weighted_02_02_05_11 : b4RawGapContribution ![2, 2, 5, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 5, 11] = b4GapPatternWeight 2 5 11 * 0 :=
      b4GapContribution_from_row 2 2 5 11 0 row_02_02_05_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_05_11

theorem row_02_02_05_12 : b4RowContribution (![2, 4, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 9, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 9 + 21 = 36
    decide
  have hzsq : (∑ i, (((![2, 4, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 542 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 9^2 + 21^2 = 542
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_05_12

theorem weighted_02_02_05_12 : b4RawGapContribution ![2, 2, 5, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 5, 12] = b4GapPatternWeight 2 5 12 * 0 :=
      b4GapContribution_from_row 2 2 5 12 0 row_02_02_05_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_05_12

theorem row_02_02_05_13 : b4RowContribution (![2, 4, 9, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 9, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 9 + 22 = 37
    decide
  have hzsq : (∑ i, (((![2, 4, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 585 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 9^2 + 22^2 = 585
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_05_13

theorem weighted_02_02_05_13 : b4RawGapContribution ![2, 2, 5, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 5, 13] = b4GapPatternWeight 2 5 13 * 0 :=
      b4GapContribution_from_row 2 2 5 13 0 row_02_02_05_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_05_13

def dvalues_02_02_05 : Fin 14 → ℕ := ![0, 0, 0, 0, 2520, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_02_05

theorem dblock_02_02_05 : b4GapPatternDBlock 2 2 5 = 2520 := by
  calc
    b4GapPatternDBlock 2 2 5 = ∑ d : Fin 14, dvalues_02_02_05 d := by
      apply b4GapDBlock_of_rows 2 2 5 dvalues_02_02_05
      intro d
      fin_cases d
      · exact weighted_02_02_05_00
      · exact weighted_02_02_05_01
      · exact weighted_02_02_05_02
      · exact weighted_02_02_05_03
      · exact weighted_02_02_05_04
      · exact weighted_02_02_05_05
      · exact weighted_02_02_05_06
      · exact weighted_02_02_05_07
      · exact weighted_02_02_05_08
      · exact weighted_02_02_05_09
      · exact weighted_02_02_05_10
      · exact weighted_02_02_05_11
      · exact weighted_02_02_05_12
      · exact weighted_02_02_05_13
    _ = 2520 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_02_05

end Paper7MomentGapNumeric
