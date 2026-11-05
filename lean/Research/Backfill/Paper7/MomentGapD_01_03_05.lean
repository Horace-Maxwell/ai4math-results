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

theorem row_01_03_05_00 : b4RowContribution (![1, 4, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 9, 9] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 9 + 9 = 23
    decide
  have hzsq : (∑ i, (((![1, 4, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 179 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 9^2 + 9^2 = 179
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_05_00

theorem weighted_01_03_05_00 : b4RawGapContribution ![1, 3, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 5, 0] = b4GapPatternWeight 3 5 0 * 0 :=
      b4GapContribution_from_row 1 3 5 0 0 row_01_03_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_00

theorem row_01_03_05_01 : b4RowContribution (![1, 4, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 9, 10] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 9 + 10 = 24
    decide
  have hzsq : (∑ i, (((![1, 4, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 198 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 9^2 + 10^2 = 198
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_05_01

theorem weighted_01_03_05_01 : b4RawGapContribution ![1, 3, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 5, 1] = b4GapPatternWeight 3 5 1 * 0 :=
      b4GapContribution_from_row 1 3 5 1 0 row_01_03_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_01

def layers_01_03_05_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 10, 10, 10, 10, 9, 7, 5, 3, 1, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 35, 45, 55, 65, 75, 84, 91, 95, 95, 91, 84, 75, 65, 55]]
#print axioms Paper7MomentGapNumeric.layers_01_03_05_02

theorem cells_01_03_05_02 : QTableValid (![1, 4, 9, 11] : Fin 4 → ℕ) layers_01_03_05_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_05_02

theorem valid_01_03_05_02 :
    SparseRowValid (![1, 4, 9, 11] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_03_05_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 9, 11] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 9 + 11 = 25
      decide
    have hzsq : (∑ i, (((![1, 4, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 219 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 9^2 + 11^2 = 219
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_05_02
#print axioms Paper7MomentGapNumeric.valid_01_03_05_02

def qvalues_01_03_05_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 75, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_05_02

theorem row_01_03_05_02 : b4RowContribution (![1, 4, 9, 11] : Fin 4 → ℕ) = 75 := by
  calc
    b4RowContribution (![1, 4, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_03_05_02) :=
      sparseRow_sound (![1, 4, 9, 11] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_03_05_02) valid_01_03_05_02
    _ = 75 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_05_02 Q := by
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
        _ = 75 := by decide
#print axioms Paper7MomentGapNumeric.row_01_03_05_02

theorem weighted_01_03_05_02 : b4RawGapContribution ![1, 3, 5, 2] = 1800 := by
  calc
    b4RawGapContribution ![1, 3, 5, 2] = b4GapPatternWeight 3 5 2 * 75 :=
      b4GapContribution_from_row 1 3 5 2 75 row_01_03_05_02
    _ = 1800 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_02

theorem row_01_03_05_03 : b4RowContribution (![1, 4, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 9, 12] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 9 + 12 = 26
    decide
  have hzsq : (∑ i, (((![1, 4, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 242 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 9^2 + 12^2 = 242
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_05_03

theorem weighted_01_03_05_03 : b4RawGapContribution ![1, 3, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 5, 3] = b4GapPatternWeight 3 5 3 * 0 :=
      b4GapContribution_from_row 1 3 5 3 0 row_01_03_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_03

theorem row_01_03_05_04 : b4RowContribution (![1, 4, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 9, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 9 + 13 = 27
    decide
  have hzsq : (∑ i, (((![1, 4, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 267 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 9^2 + 13^2 = 267
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_05_04

theorem weighted_01_03_05_04 : b4RawGapContribution ![1, 3, 5, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 5, 4] = b4GapPatternWeight 3 5 4 * 0 :=
      b4GapContribution_from_row 1 3 5 4 0 row_01_03_05_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_04

theorem row_01_03_05_05 : b4RowContribution (![1, 4, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 9, 14] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 9 + 14 = 28
    decide
  have hzsq : (∑ i, (((![1, 4, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 294 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 9^2 + 14^2 = 294
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_05_05

theorem weighted_01_03_05_05 : b4RawGapContribution ![1, 3, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 5, 5] = b4GapPatternWeight 3 5 5 * 0 :=
      b4GapContribution_from_row 1 3 5 5 0 row_01_03_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_05

theorem row_01_03_05_06 : b4RowContribution (![1, 4, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 9, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 9 + 15 = 29
    decide
  have hzsq : (∑ i, (((![1, 4, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 323 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 9^2 + 15^2 = 323
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_05_06

theorem weighted_01_03_05_06 : b4RawGapContribution ![1, 3, 5, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 5, 6] = b4GapPatternWeight 3 5 6 * 0 :=
      b4GapContribution_from_row 1 3 5 6 0 row_01_03_05_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_06

theorem row_01_03_05_07 : b4RowContribution (![1, 4, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 9, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 9 + 16 = 30
    decide
  have hzsq : (∑ i, (((![1, 4, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 354 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 9^2 + 16^2 = 354
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_05_07

theorem weighted_01_03_05_07 : b4RawGapContribution ![1, 3, 5, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 5, 7] = b4GapPatternWeight 3 5 7 * 0 :=
      b4GapContribution_from_row 1 3 5 7 0 row_01_03_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_07

theorem row_01_03_05_08 : b4RowContribution (![1, 4, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 9, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 9 + 17 = 31
    decide
  have hzsq : (∑ i, (((![1, 4, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 387 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 9^2 + 17^2 = 387
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_05_08

theorem weighted_01_03_05_08 : b4RawGapContribution ![1, 3, 5, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 5, 8] = b4GapPatternWeight 3 5 8 * 0 :=
      b4GapContribution_from_row 1 3 5 8 0 row_01_03_05_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_08

theorem row_01_03_05_09 : b4RowContribution (![1, 4, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 9, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 9 + 18 = 32
    decide
  have hzsq : (∑ i, (((![1, 4, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 422 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 9^2 + 18^2 = 422
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_05_09

theorem weighted_01_03_05_09 : b4RawGapContribution ![1, 3, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 5, 9] = b4GapPatternWeight 3 5 9 * 0 :=
      b4GapContribution_from_row 1 3 5 9 0 row_01_03_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_09

theorem row_01_03_05_10 : b4RowContribution (![1, 4, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 9, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 9 + 19 = 33
    decide
  have hzsq : (∑ i, (((![1, 4, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 459 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 9^2 + 19^2 = 459
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_05_10

theorem weighted_01_03_05_10 : b4RawGapContribution ![1, 3, 5, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 5, 10] = b4GapPatternWeight 3 5 10 * 0 :=
      b4GapContribution_from_row 1 3 5 10 0 row_01_03_05_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_10

theorem row_01_03_05_11 : b4RowContribution (![1, 4, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 9, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 9 + 20 = 34
    decide
  have hzsq : (∑ i, (((![1, 4, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 498 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 9^2 + 20^2 = 498
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_05_11

theorem weighted_01_03_05_11 : b4RawGapContribution ![1, 3, 5, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 5, 11] = b4GapPatternWeight 3 5 11 * 0 :=
      b4GapContribution_from_row 1 3 5 11 0 row_01_03_05_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_11

theorem row_01_03_05_12 : b4RowContribution (![1, 4, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 9, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 9 + 21 = 35
    decide
  have hzsq : (∑ i, (((![1, 4, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 539 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 9^2 + 21^2 = 539
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_05_12

theorem weighted_01_03_05_12 : b4RawGapContribution ![1, 3, 5, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 5, 12] = b4GapPatternWeight 3 5 12 * 0 :=
      b4GapContribution_from_row 1 3 5 12 0 row_01_03_05_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_12

theorem row_01_03_05_13 : b4RowContribution (![1, 4, 9, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 9, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 9 + 22 = 36
    decide
  have hzsq : (∑ i, (((![1, 4, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 582 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 9^2 + 22^2 = 582
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_05_13

theorem weighted_01_03_05_13 : b4RawGapContribution ![1, 3, 5, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 5, 13] = b4GapPatternWeight 3 5 13 * 0 :=
      b4GapContribution_from_row 1 3 5 13 0 row_01_03_05_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_13

theorem row_01_03_05_14 : b4RowContribution (![1, 4, 9, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 9, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 9 + 23 = 37
    decide
  have hzsq : (∑ i, (((![1, 4, 9, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 627 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 9^2 + 23^2 = 627
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_05_14

theorem weighted_01_03_05_14 : b4RawGapContribution ![1, 3, 5, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 5, 14] = b4GapPatternWeight 3 5 14 * 0 :=
      b4GapContribution_from_row 1 3 5 14 0 row_01_03_05_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_05_14

def dvalues_01_03_05 : Fin 15 → ℕ := ![0, 0, 1800, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_03_05

theorem dblock_01_03_05 : b4GapPatternDBlock 1 3 5 = 1800 := by
  calc
    b4GapPatternDBlock 1 3 5 = ∑ d : Fin 15, dvalues_01_03_05 d := by
      apply b4GapDBlock_of_rows 1 3 5 dvalues_01_03_05
      intro d
      fin_cases d
      · exact weighted_01_03_05_00
      · exact weighted_01_03_05_01
      · exact weighted_01_03_05_02
      · exact weighted_01_03_05_03
      · exact weighted_01_03_05_04
      · exact weighted_01_03_05_05
      · exact weighted_01_03_05_06
      · exact weighted_01_03_05_07
      · exact weighted_01_03_05_08
      · exact weighted_01_03_05_09
      · exact weighted_01_03_05_10
      · exact weighted_01_03_05_11
      · exact weighted_01_03_05_12
      · exact weighted_01_03_05_13
      · exact weighted_01_03_05_14
    _ = 1800 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_03_05

end Paper7MomentGapNumeric
