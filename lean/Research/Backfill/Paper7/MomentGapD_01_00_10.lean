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

theorem row_01_00_10_00 : b4RowContribution (![1, 1, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 11, 11] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 11 + 11 = 24
    decide
  have hzsq : (∑ i, (((![1, 1, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 244 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 11^2 + 11^2 = 244
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_10_00

theorem weighted_01_00_10_00 : b4RawGapContribution ![1, 0, 10, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 10, 0] = b4GapPatternWeight 0 10 0 * 0 :=
      b4GapContribution_from_row 1 0 10 0 0 row_01_00_10_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_10_00

theorem row_01_00_10_01 : b4RowContribution (![1, 1, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 11, 12] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 11 + 12 = 25
    decide
  have hzsq : (∑ i, (((![1, 1, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 267 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 11^2 + 12^2 = 267
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_10_01

theorem weighted_01_00_10_01 : b4RawGapContribution ![1, 0, 10, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 10, 1] = b4GapPatternWeight 0 10 1 * 0 :=
      b4GapContribution_from_row 1 0 10 1 0 row_01_00_10_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_10_01

theorem row_01_00_10_02 : b4RowContribution (![1, 1, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 11, 13] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 11 + 13 = 26
    decide
  have hzsq : (∑ i, (((![1, 1, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 292 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 11^2 + 13^2 = 292
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_10_02

theorem weighted_01_00_10_02 : b4RawGapContribution ![1, 0, 10, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 10, 2] = b4GapPatternWeight 0 10 2 * 0 :=
      b4GapContribution_from_row 1 0 10 2 0 row_01_00_10_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_10_02

theorem row_01_00_10_03 : b4RowContribution (![1, 1, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 11, 14] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 11 + 14 = 27
    decide
  have hzsq : (∑ i, (((![1, 1, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 319 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 11^2 + 14^2 = 319
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_10_03

theorem weighted_01_00_10_03 : b4RawGapContribution ![1, 0, 10, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 10, 3] = b4GapPatternWeight 0 10 3 * 0 :=
      b4GapContribution_from_row 1 0 10 3 0 row_01_00_10_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_10_03

theorem row_01_00_10_04 : b4RowContribution (![1, 1, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 11, 15] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 11 + 15 = 28
    decide
  have hzsq : (∑ i, (((![1, 1, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 348 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 11^2 + 15^2 = 348
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_10_04

theorem weighted_01_00_10_04 : b4RawGapContribution ![1, 0, 10, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 10, 4] = b4GapPatternWeight 0 10 4 * 0 :=
      b4GapContribution_from_row 1 0 10 4 0 row_01_00_10_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_10_04

theorem row_01_00_10_05 : b4RowContribution (![1, 1, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 11, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 11 + 16 = 29
    decide
  have hzsq : (∑ i, (((![1, 1, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 379 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 11^2 + 16^2 = 379
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_10_05

theorem weighted_01_00_10_05 : b4RawGapContribution ![1, 0, 10, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 10, 5] = b4GapPatternWeight 0 10 5 * 0 :=
      b4GapContribution_from_row 1 0 10 5 0 row_01_00_10_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_10_05

theorem row_01_00_10_06 : b4RowContribution (![1, 1, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 11, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 11 + 17 = 30
    decide
  have hzsq : (∑ i, (((![1, 1, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 412 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 11^2 + 17^2 = 412
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_10_06

theorem weighted_01_00_10_06 : b4RawGapContribution ![1, 0, 10, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 10, 6] = b4GapPatternWeight 0 10 6 * 0 :=
      b4GapContribution_from_row 1 0 10 6 0 row_01_00_10_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_10_06

theorem row_01_00_10_07 : b4RowContribution (![1, 1, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 11, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 11 + 18 = 31
    decide
  have hzsq : (∑ i, (((![1, 1, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 447 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 11^2 + 18^2 = 447
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_10_07

theorem weighted_01_00_10_07 : b4RawGapContribution ![1, 0, 10, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 10, 7] = b4GapPatternWeight 0 10 7 * 0 :=
      b4GapContribution_from_row 1 0 10 7 0 row_01_00_10_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_10_07

theorem row_01_00_10_08 : b4RowContribution (![1, 1, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 11, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 11 + 19 = 32
    decide
  have hzsq : (∑ i, (((![1, 1, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 484 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 11^2 + 19^2 = 484
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_10_08

theorem weighted_01_00_10_08 : b4RawGapContribution ![1, 0, 10, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 10, 8] = b4GapPatternWeight 0 10 8 * 0 :=
      b4GapContribution_from_row 1 0 10 8 0 row_01_00_10_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_10_08

theorem row_01_00_10_09 : b4RowContribution (![1, 1, 11, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 11, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 11 + 20 = 33
    decide
  have hzsq : (∑ i, (((![1, 1, 11, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 523 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 11^2 + 20^2 = 523
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_10_09

theorem weighted_01_00_10_09 : b4RawGapContribution ![1, 0, 10, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 10, 9] = b4GapPatternWeight 0 10 9 * 0 :=
      b4GapContribution_from_row 1 0 10 9 0 row_01_00_10_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_10_09

def layers_01_00_10_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 47, 48, 48, 48, 48, 48, 48]]
#print axioms Paper7MomentGapNumeric.layers_01_00_10_10

theorem cells_01_00_10_10 : QTableValid (![1, 1, 11, 21] : Fin 4 → ℕ) layers_01_00_10_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_10_10

theorem valid_01_00_10_10 :
    SparseRowValid (![1, 1, 11, 21] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_01_00_10_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 11, 21] : Fin 4 → ℕ) i) = 34 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 11 + 21 = 34
      decide
    have hzsq : (∑ i, (((![1, 1, 11, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 564 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 11^2 + 21^2 = 564
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_10_10
#print axioms Paper7MomentGapNumeric.valid_01_00_10_10

def qvalues_01_00_10_10 : Fin 19 → ℕ := ![0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_10_10

theorem row_01_00_10_10 : b4RowContribution (![1, 1, 11, 21] : Fin 4 → ℕ) = 12 := by
  calc
    b4RowContribution (![1, 1, 11, 21] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_01_00_10_10) :=
      sparseRow_sound (![1, 1, 11, 21] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_01_00_10_10) valid_01_00_10_10
    _ = 12 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_10_10 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_10_10

theorem weighted_01_00_10_10 : b4RawGapContribution ![1, 0, 10, 10] = 144 := by
  calc
    b4RawGapContribution ![1, 0, 10, 10] = b4GapPatternWeight 0 10 10 * 12 :=
      b4GapContribution_from_row 1 0 10 10 12 row_01_00_10_10
    _ = 144 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_10_10

theorem row_01_00_10_11 : b4RowContribution (![1, 1, 11, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 11, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 11 + 22 = 35
    decide
  have hzsq : (∑ i, (((![1, 1, 11, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 607 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 11^2 + 22^2 = 607
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_10_11

theorem weighted_01_00_10_11 : b4RawGapContribution ![1, 0, 10, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 10, 11] = b4GapPatternWeight 0 10 11 * 0 :=
      b4GapContribution_from_row 1 0 10 11 0 row_01_00_10_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_10_11

theorem row_01_00_10_12 : b4RowContribution (![1, 1, 11, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 11, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 11 + 23 = 36
    decide
  have hzsq : (∑ i, (((![1, 1, 11, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 652 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 11^2 + 23^2 = 652
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_10_12

theorem weighted_01_00_10_12 : b4RawGapContribution ![1, 0, 10, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 10, 12] = b4GapPatternWeight 0 10 12 * 0 :=
      b4GapContribution_from_row 1 0 10 12 0 row_01_00_10_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_10_12

theorem row_01_00_10_13 : b4RowContribution (![1, 1, 11, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 11, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 11 + 24 = 37
    decide
  have hzsq : (∑ i, (((![1, 1, 11, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 699 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 11^2 + 24^2 = 699
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_10_13

theorem weighted_01_00_10_13 : b4RawGapContribution ![1, 0, 10, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 10, 13] = b4GapPatternWeight 0 10 13 * 0 :=
      b4GapContribution_from_row 1 0 10 13 0 row_01_00_10_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_10_13

def dvalues_01_00_10 : Fin 14 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_00_10

theorem dblock_01_00_10 : b4GapPatternDBlock 1 0 10 = 144 := by
  calc
    b4GapPatternDBlock 1 0 10 = ∑ d : Fin 14, dvalues_01_00_10 d := by
      apply b4GapDBlock_of_rows 1 0 10 dvalues_01_00_10
      intro d
      fin_cases d
      · exact weighted_01_00_10_00
      · exact weighted_01_00_10_01
      · exact weighted_01_00_10_02
      · exact weighted_01_00_10_03
      · exact weighted_01_00_10_04
      · exact weighted_01_00_10_05
      · exact weighted_01_00_10_06
      · exact weighted_01_00_10_07
      · exact weighted_01_00_10_08
      · exact weighted_01_00_10_09
      · exact weighted_01_00_10_10
      · exact weighted_01_00_10_11
      · exact weighted_01_00_10_12
      · exact weighted_01_00_10_13
    _ = 144 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_00_10

end Paper7MomentGapNumeric
