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

theorem row_01_00_09_00 : b4RowContribution (![1, 1, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 10] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 10 = 22
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 202 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 10^2 = 202
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_00

theorem weighted_01_00_09_00 : b4RawGapContribution ![1, 0, 9, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 0] = b4GapPatternWeight 0 9 0 * 0 :=
      b4GapContribution_from_row 1 0 9 0 0 row_01_00_09_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_00

def layers_01_00_09_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 43, 43, 40, 36, 32, 28, 24, 20]]
#print axioms Paper7MomentGapNumeric.layers_01_00_09_01

theorem cells_01_00_09_01 : QTableValid (![1, 1, 10, 11] : Fin 4 → ℕ) layers_01_00_09_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_09_01

theorem valid_01_00_09_01 :
    SparseRowValid (![1, 1, 10, 11] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_00_09_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 10, 11] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 10 + 11 = 23
      decide
    have hzsq : (∑ i, (((![1, 1, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 223 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 10^2 + 11^2 = 223
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_09_01
#print axioms Paper7MomentGapNumeric.valid_01_00_09_01

def qvalues_01_00_09_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_09_01

theorem row_01_00_09_01 : b4RowContribution (![1, 1, 10, 11] : Fin 4 → ℕ) = 40 := by
  calc
    b4RowContribution (![1, 1, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_00_09_01) :=
      sparseRow_sound (![1, 1, 10, 11] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_00_09_01) valid_01_00_09_01
    _ = 40 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_09_01 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 40 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_09_01

theorem weighted_01_00_09_01 : b4RawGapContribution ![1, 0, 9, 1] = 480 := by
  calc
    b4RawGapContribution ![1, 0, 9, 1] = b4GapPatternWeight 0 9 1 * 40 :=
      b4GapContribution_from_row 1 0 9 1 40 row_01_00_09_01
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_01

theorem row_01_00_09_02 : b4RowContribution (![1, 1, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 12] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 12 = 24
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 246 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 12^2 = 246
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_02

theorem weighted_01_00_09_02 : b4RawGapContribution ![1, 0, 9, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 2] = b4GapPatternWeight 0 9 2 * 0 :=
      b4GapContribution_from_row 1 0 9 2 0 row_01_00_09_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_02

theorem row_01_00_09_03 : b4RowContribution (![1, 1, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 13] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 13 = 25
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 271 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 13^2 = 271
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_03

theorem weighted_01_00_09_03 : b4RawGapContribution ![1, 0, 9, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 3] = b4GapPatternWeight 0 9 3 * 0 :=
      b4GapContribution_from_row 1 0 9 3 0 row_01_00_09_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_03

theorem row_01_00_09_04 : b4RowContribution (![1, 1, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 14] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 14 = 26
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 298 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 14^2 = 298
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_04

theorem weighted_01_00_09_04 : b4RawGapContribution ![1, 0, 9, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 4] = b4GapPatternWeight 0 9 4 * 0 :=
      b4GapContribution_from_row 1 0 9 4 0 row_01_00_09_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_04

theorem row_01_00_09_05 : b4RowContribution (![1, 1, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 15] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 15 = 27
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 327 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 15^2 = 327
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_05

theorem weighted_01_00_09_05 : b4RawGapContribution ![1, 0, 9, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 5] = b4GapPatternWeight 0 9 5 * 0 :=
      b4GapContribution_from_row 1 0 9 5 0 row_01_00_09_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_05

theorem row_01_00_09_06 : b4RowContribution (![1, 1, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 16] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 16 = 28
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 358 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 16^2 = 358
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_06

theorem weighted_01_00_09_06 : b4RawGapContribution ![1, 0, 9, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 6] = b4GapPatternWeight 0 9 6 * 0 :=
      b4GapContribution_from_row 1 0 9 6 0 row_01_00_09_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_06

theorem row_01_00_09_07 : b4RowContribution (![1, 1, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 17] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 17 = 29
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 391 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 17^2 = 391
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_07

theorem weighted_01_00_09_07 : b4RawGapContribution ![1, 0, 9, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 7] = b4GapPatternWeight 0 9 7 * 0 :=
      b4GapContribution_from_row 1 0 9 7 0 row_01_00_09_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_07

theorem row_01_00_09_08 : b4RowContribution (![1, 1, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 18] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 18 = 30
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 426 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 18^2 = 426
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_08

theorem weighted_01_00_09_08 : b4RawGapContribution ![1, 0, 9, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 8] = b4GapPatternWeight 0 9 8 * 0 :=
      b4GapContribution_from_row 1 0 9 8 0 row_01_00_09_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_08

theorem row_01_00_09_09 : b4RowContribution (![1, 1, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 19] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 19 = 31
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 463 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 19^2 = 463
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_09

theorem weighted_01_00_09_09 : b4RawGapContribution ![1, 0, 9, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 9] = b4GapPatternWeight 0 9 9 * 0 :=
      b4GapContribution_from_row 1 0 9 9 0 row_01_00_09_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_09

theorem row_01_00_09_10 : b4RowContribution (![1, 1, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 20] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 20 = 32
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 502 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 20^2 = 502
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_10

theorem weighted_01_00_09_10 : b4RawGapContribution ![1, 0, 9, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 10] = b4GapPatternWeight 0 9 10 * 0 :=
      b4GapContribution_from_row 1 0 9 10 0 row_01_00_09_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_10

theorem row_01_00_09_11 : b4RowContribution (![1, 1, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 21] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 21 = 33
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 543 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 21^2 = 543
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_11

theorem weighted_01_00_09_11 : b4RawGapContribution ![1, 0, 9, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 11] = b4GapPatternWeight 0 9 11 * 0 :=
      b4GapContribution_from_row 1 0 9 11 0 row_01_00_09_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_11

theorem row_01_00_09_12 : b4RowContribution (![1, 1, 10, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 22] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 22 = 34
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 586 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 22^2 = 586
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_12

theorem weighted_01_00_09_12 : b4RawGapContribution ![1, 0, 9, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 12] = b4GapPatternWeight 0 9 12 * 0 :=
      b4GapContribution_from_row 1 0 9 12 0 row_01_00_09_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_12

theorem row_01_00_09_13 : b4RowContribution (![1, 1, 10, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 23] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 23 = 35
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 631 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 23^2 = 631
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_13

theorem weighted_01_00_09_13 : b4RawGapContribution ![1, 0, 9, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 13] = b4GapPatternWeight 0 9 13 * 0 :=
      b4GapContribution_from_row 1 0 9 13 0 row_01_00_09_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_13

theorem row_01_00_09_14 : b4RowContribution (![1, 1, 10, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 24] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 24 = 36
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 678 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 24^2 = 678
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_14

theorem weighted_01_00_09_14 : b4RawGapContribution ![1, 0, 9, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 14] = b4GapPatternWeight 0 9 14 * 0 :=
      b4GapContribution_from_row 1 0 9 14 0 row_01_00_09_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_14

theorem row_01_00_09_15 : b4RowContribution (![1, 1, 10, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 10, 25] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 10 + 25 = 37
    decide
  have hzsq : (∑ i, (((![1, 1, 10, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 727 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 10^2 + 25^2 = 727
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_09_15

theorem weighted_01_00_09_15 : b4RawGapContribution ![1, 0, 9, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 9, 15] = b4GapPatternWeight 0 9 15 * 0 :=
      b4GapContribution_from_row 1 0 9 15 0 row_01_00_09_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_09_15

def dvalues_01_00_09 : Fin 16 → ℕ := ![0, 480, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_00_09

theorem dblock_01_00_09 : b4GapPatternDBlock 1 0 9 = 480 := by
  calc
    b4GapPatternDBlock 1 0 9 = ∑ d : Fin 16, dvalues_01_00_09 d := by
      apply b4GapDBlock_of_rows 1 0 9 dvalues_01_00_09
      intro d
      fin_cases d
      · exact weighted_01_00_09_00
      · exact weighted_01_00_09_01
      · exact weighted_01_00_09_02
      · exact weighted_01_00_09_03
      · exact weighted_01_00_09_04
      · exact weighted_01_00_09_05
      · exact weighted_01_00_09_06
      · exact weighted_01_00_09_07
      · exact weighted_01_00_09_08
      · exact weighted_01_00_09_09
      · exact weighted_01_00_09_10
      · exact weighted_01_00_09_11
      · exact weighted_01_00_09_12
      · exact weighted_01_00_09_13
      · exact weighted_01_00_09_14
      · exact weighted_01_00_09_15
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_00_09

end Paper7MomentGapNumeric
