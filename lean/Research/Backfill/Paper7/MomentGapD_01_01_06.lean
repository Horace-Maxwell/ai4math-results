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

theorem row_01_01_06_00 : b4RowContribution (![1, 2, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 8] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 8 = 19
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 133 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 8^2 = 133
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_00

theorem weighted_01_01_06_00 : b4RawGapContribution ![1, 1, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 0] = b4GapPatternWeight 1 6 0 * 0 :=
      b4GapContribution_from_row 1 1 6 0 0 row_01_01_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_00

theorem row_01_01_06_01 : b4RowContribution (![1, 2, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 9] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 9 = 20
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 150 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 9^2 = 150
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_01

theorem weighted_01_01_06_01 : b4RawGapContribution ![1, 1, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 1] = b4GapPatternWeight 1 6 1 * 0 :=
      b4GapContribution_from_row 1 1 6 1 0 row_01_01_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_01

theorem row_01_01_06_02 : b4RowContribution (![1, 2, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 10] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 10 = 21
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 169 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 10^2 = 169
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_02

theorem weighted_01_01_06_02 : b4RawGapContribution ![1, 1, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 2] = b4GapPatternWeight 1 6 2 * 0 :=
      b4GapContribution_from_row 1 1 6 2 0 row_01_01_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_02

theorem row_01_01_06_03 : b4RowContribution (![1, 2, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 11] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 11 = 22
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 190 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 11^2 = 190
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_03

theorem weighted_01_01_06_03 : b4RawGapContribution ![1, 1, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 3] = b4GapPatternWeight 1 6 3 * 0 :=
      b4GapContribution_from_row 1 1 6 3 0 row_01_01_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_03

theorem row_01_01_06_04 : b4RowContribution (![1, 2, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 12] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 12 = 23
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 213 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 12^2 = 213
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_04

theorem weighted_01_01_06_04 : b4RawGapContribution ![1, 1, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 4] = b4GapPatternWeight 1 6 4 * 0 :=
      b4GapContribution_from_row 1 1 6 4 0 row_01_01_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_04

def layers_01_01_06_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 27, 33, 39, 45, 50, 53, 54, 54, 54, 53, 50, 45, 39, 33]]
#print axioms Paper7MomentGapNumeric.layers_01_01_06_05

theorem cells_01_01_06_05 : QTableValid (![1, 2, 8, 13] : Fin 4 → ℕ) layers_01_01_06_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_06_05

theorem valid_01_01_06_05 :
    SparseRowValid (![1, 2, 8, 13] : Fin 4 → ℕ) ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_01_06_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 8, 13] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 8 + 13 = 24
      decide
    have hzsq : (∑ i, (((![1, 2, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 238 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 8^2 + 13^2 = 238
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_06_05
#print axioms Paper7MomentGapNumeric.valid_01_01_06_05

def qvalues_01_01_06_05 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_06_05

theorem row_01_01_06_05 : b4RowContribution (![1, 2, 8, 13] : Fin 4 → ℕ) = 43 := by
  calc
    b4RowContribution (![1, 2, 8, 13] : Fin 4 → ℕ) =
        sparseRowValue ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_01_06_05) :=
      sparseRow_sound (![1, 2, 8, 13] : Fin 4 → ℕ) ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_01_06_05) valid_01_01_06_05
    _ = 43 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_06_05 Q := by
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
        _ = 43 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_06_05

theorem weighted_01_01_06_05 : b4RawGapContribution ![1, 1, 6, 5] = 1032 := by
  calc
    b4RawGapContribution ![1, 1, 6, 5] = b4GapPatternWeight 1 6 5 * 43 :=
      b4GapContribution_from_row 1 1 6 5 43 row_01_01_06_05
    _ = 1032 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_05

theorem row_01_01_06_06 : b4RowContribution (![1, 2, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 14] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 14 = 25
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 265 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 14^2 = 265
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_06

theorem weighted_01_01_06_06 : b4RawGapContribution ![1, 1, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 6] = b4GapPatternWeight 1 6 6 * 0 :=
      b4GapContribution_from_row 1 1 6 6 0 row_01_01_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_06

theorem row_01_01_06_07 : b4RowContribution (![1, 2, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 15] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 15 = 26
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 294 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 15^2 = 294
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_07

theorem weighted_01_01_06_07 : b4RawGapContribution ![1, 1, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 7] = b4GapPatternWeight 1 6 7 * 0 :=
      b4GapContribution_from_row 1 1 6 7 0 row_01_01_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_07

theorem row_01_01_06_08 : b4RowContribution (![1, 2, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 16] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 16 = 27
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 16^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_08

theorem weighted_01_01_06_08 : b4RawGapContribution ![1, 1, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 8] = b4GapPatternWeight 1 6 8 * 0 :=
      b4GapContribution_from_row 1 1 6 8 0 row_01_01_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_08

theorem row_01_01_06_09 : b4RowContribution (![1, 2, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 17] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 17 = 28
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 358 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 17^2 = 358
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_09

theorem weighted_01_01_06_09 : b4RawGapContribution ![1, 1, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 9] = b4GapPatternWeight 1 6 9 * 0 :=
      b4GapContribution_from_row 1 1 6 9 0 row_01_01_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_09

theorem row_01_01_06_10 : b4RowContribution (![1, 2, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 18] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 18 = 29
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 393 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 18^2 = 393
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_10

theorem weighted_01_01_06_10 : b4RawGapContribution ![1, 1, 6, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 10] = b4GapPatternWeight 1 6 10 * 0 :=
      b4GapContribution_from_row 1 1 6 10 0 row_01_01_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_10

theorem row_01_01_06_11 : b4RowContribution (![1, 2, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 19] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 19 = 30
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 430 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 19^2 = 430
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_11

theorem weighted_01_01_06_11 : b4RawGapContribution ![1, 1, 6, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 11] = b4GapPatternWeight 1 6 11 * 0 :=
      b4GapContribution_from_row 1 1 6 11 0 row_01_01_06_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_11

theorem row_01_01_06_12 : b4RowContribution (![1, 2, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 20] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 20 = 31
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 469 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 20^2 = 469
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_12

theorem weighted_01_01_06_12 : b4RawGapContribution ![1, 1, 6, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 12] = b4GapPatternWeight 1 6 12 * 0 :=
      b4GapContribution_from_row 1 1 6 12 0 row_01_01_06_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_12

theorem row_01_01_06_13 : b4RowContribution (![1, 2, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 21] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 21 = 32
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 510 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 21^2 = 510
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_13

theorem weighted_01_01_06_13 : b4RawGapContribution ![1, 1, 6, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 13] = b4GapPatternWeight 1 6 13 * 0 :=
      b4GapContribution_from_row 1 1 6 13 0 row_01_01_06_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_13

theorem row_01_01_06_14 : b4RowContribution (![1, 2, 8, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 22] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 22 = 33
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 553 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 22^2 = 553
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_14

theorem weighted_01_01_06_14 : b4RawGapContribution ![1, 1, 6, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 14] = b4GapPatternWeight 1 6 14 * 0 :=
      b4GapContribution_from_row 1 1 6 14 0 row_01_01_06_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_14

theorem row_01_01_06_15 : b4RowContribution (![1, 2, 8, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 23] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 23 = 34
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 598 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 23^2 = 598
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_15

theorem weighted_01_01_06_15 : b4RawGapContribution ![1, 1, 6, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 15] = b4GapPatternWeight 1 6 15 * 0 :=
      b4GapContribution_from_row 1 1 6 15 0 row_01_01_06_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_15

theorem row_01_01_06_16 : b4RowContribution (![1, 2, 8, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 24] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 24 = 35
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 645 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 24^2 = 645
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_16

theorem weighted_01_01_06_16 : b4RawGapContribution ![1, 1, 6, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 16] = b4GapPatternWeight 1 6 16 * 0 :=
      b4GapContribution_from_row 1 1 6 16 0 row_01_01_06_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_16

theorem row_01_01_06_17 : b4RowContribution (![1, 2, 8, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 25] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 25 = 36
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 694 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 25^2 = 694
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_17

theorem weighted_01_01_06_17 : b4RawGapContribution ![1, 1, 6, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 17] = b4GapPatternWeight 1 6 17 * 0 :=
      b4GapContribution_from_row 1 1 6 17 0 row_01_01_06_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_17

theorem row_01_01_06_18 : b4RowContribution (![1, 2, 8, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 8, 26] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 8 + 26 = 37
    decide
  have hzsq : (∑ i, (((![1, 2, 8, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 745 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 8^2 + 26^2 = 745
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_06_18

theorem weighted_01_01_06_18 : b4RawGapContribution ![1, 1, 6, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 6, 18] = b4GapPatternWeight 1 6 18 * 0 :=
      b4GapContribution_from_row 1 1 6 18 0 row_01_01_06_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_06_18

def dvalues_01_01_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 1032, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_01_06

theorem dblock_01_01_06 : b4GapPatternDBlock 1 1 6 = 1032 := by
  calc
    b4GapPatternDBlock 1 1 6 = ∑ d : Fin 19, dvalues_01_01_06 d := by
      apply b4GapDBlock_of_rows 1 1 6 dvalues_01_01_06
      intro d
      fin_cases d
      · exact weighted_01_01_06_00
      · exact weighted_01_01_06_01
      · exact weighted_01_01_06_02
      · exact weighted_01_01_06_03
      · exact weighted_01_01_06_04
      · exact weighted_01_01_06_05
      · exact weighted_01_01_06_06
      · exact weighted_01_01_06_07
      · exact weighted_01_01_06_08
      · exact weighted_01_01_06_09
      · exact weighted_01_01_06_10
      · exact weighted_01_01_06_11
      · exact weighted_01_01_06_12
      · exact weighted_01_01_06_13
      · exact weighted_01_01_06_14
      · exact weighted_01_01_06_15
      · exact weighted_01_01_06_16
      · exact weighted_01_01_06_17
      · exact weighted_01_01_06_18
    _ = 1032 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_01_06

end Paper7MomentGapNumeric
