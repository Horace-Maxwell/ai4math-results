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

def layers_01_05_04_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 14, 14, 14, 14, 13, 11, 9, 7, 5, 3, 1, 0], ![1, 4, 9, 16, 25, 36, 49, 63, 77, 91, 105, 117, 125, 129, 129, 125, 117, 105, 91]]
#print axioms Paper7MomentGapNumeric.layers_01_05_04_00

theorem cells_01_05_04_00 : QTableValid (![1, 6, 10, 10] : Fin 4 → ℕ) layers_01_05_04_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_05_04_00

theorem valid_01_05_04_00 :
    SparseRowValid (![1, 6, 10, 10] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_01_05_04_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 6, 10, 10] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 1 + 6 + 10 + 10 = 27
      decide
    have hzsq : (∑ i, (((![1, 6, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 237 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 6^2 + 10^2 + 10^2 = 237
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_05_04_00
#print axioms Paper7MomentGapNumeric.valid_01_05_04_00

def qvalues_01_05_04_00 : Fin 19 → ℕ := ![0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_05_04_00

theorem row_01_05_04_00 : b4RowContribution (![1, 6, 10, 10] : Fin 4 → ℕ) = 16 := by
  calc
    b4RowContribution (![1, 6, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_01_05_04_00) :=
      sparseRow_sound (![1, 6, 10, 10] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_01_05_04_00) valid_01_05_04_00
    _ = 16 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_05_04_00 Q := by
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
        _ = 16 := by decide
#print axioms Paper7MomentGapNumeric.row_01_05_04_00

theorem weighted_01_05_04_00 : b4RawGapContribution ![1, 5, 4, 0] = 192 := by
  calc
    b4RawGapContribution ![1, 5, 4, 0] = b4GapPatternWeight 5 4 0 * 16 :=
      b4GapContribution_from_row 1 5 4 0 16 row_01_05_04_00
    _ = 192 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_04_00

theorem row_01_05_04_01 : b4RowContribution (![1, 6, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 10, 11] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 10 + 11 = 28
    decide
  have hzsq : (∑ i, (((![1, 6, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 258 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 10^2 + 11^2 = 258
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_04_01

theorem weighted_01_05_04_01 : b4RawGapContribution ![1, 5, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 4, 1] = b4GapPatternWeight 5 4 1 * 0 :=
      b4GapContribution_from_row 1 5 4 1 0 row_01_05_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_04_01

def layers_01_05_04_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 14, 14, 14, 14, 13, 11, 9, 7, 5, 3, 1, 0], ![1, 4, 9, 16, 25, 36, 49, 63, 77, 91, 105, 118, 129, 137, 141, 141, 137, 129, 118]]
#print axioms Paper7MomentGapNumeric.layers_01_05_04_02

theorem cells_01_05_04_02 : QTableValid (![1, 6, 10, 12] : Fin 4 → ℕ) layers_01_05_04_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_05_04_02

theorem valid_01_05_04_02 :
    SparseRowValid (![1, 6, 10, 12] : Fin 4 → ℕ) ({2, 8} : Finset (Fin 19)) (fun _ => layers_01_05_04_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 6, 10, 12] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 1 + 6 + 10 + 12 = 29
      decide
    have hzsq : (∑ i, (((![1, 6, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 281 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 6^2 + 10^2 + 12^2 = 281
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_05_04_02
#print axioms Paper7MomentGapNumeric.valid_01_05_04_02

def qvalues_01_05_04_02 : Fin 19 → ℕ := ![0, 0, 9, 0, 0, 0, 0, 0, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_05_04_02

theorem row_01_05_04_02 : b4RowContribution (![1, 6, 10, 12] : Fin 4 → ℕ) = 86 := by
  calc
    b4RowContribution (![1, 6, 10, 12] : Fin 4 → ℕ) =
        sparseRowValue ({2, 8} : Finset (Fin 19)) (fun _ => layers_01_05_04_02) :=
      sparseRow_sound (![1, 6, 10, 12] : Fin 4 → ℕ) ({2, 8} : Finset (Fin 19)) (fun _ => layers_01_05_04_02) valid_01_05_04_02
    _ = 86 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_05_04_02 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
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
        _ = 86 := by decide
#print axioms Paper7MomentGapNumeric.row_01_05_04_02

theorem weighted_01_05_04_02 : b4RawGapContribution ![1, 5, 4, 2] = 2064 := by
  calc
    b4RawGapContribution ![1, 5, 4, 2] = b4GapPatternWeight 5 4 2 * 86 :=
      b4GapContribution_from_row 1 5 4 2 86 row_01_05_04_02
    _ = 2064 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_04_02

theorem row_01_05_04_03 : b4RowContribution (![1, 6, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 10, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 10 + 13 = 30
    decide
  have hzsq : (∑ i, (((![1, 6, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 10^2 + 13^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_04_03

theorem weighted_01_05_04_03 : b4RawGapContribution ![1, 5, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 4, 3] = b4GapPatternWeight 5 4 3 * 0 :=
      b4GapContribution_from_row 1 5 4 3 0 row_01_05_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_04_03

theorem row_01_05_04_04 : b4RowContribution (![1, 6, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 10, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 10 + 14 = 31
    decide
  have hzsq : (∑ i, (((![1, 6, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 333 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 10^2 + 14^2 = 333
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_04_04

theorem weighted_01_05_04_04 : b4RawGapContribution ![1, 5, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 4, 4] = b4GapPatternWeight 5 4 4 * 0 :=
      b4GapContribution_from_row 1 5 4 4 0 row_01_05_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_04_04

theorem row_01_05_04_05 : b4RowContribution (![1, 6, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 10, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 10 + 15 = 32
    decide
  have hzsq : (∑ i, (((![1, 6, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 362 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 10^2 + 15^2 = 362
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_04_05

theorem weighted_01_05_04_05 : b4RawGapContribution ![1, 5, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 4, 5] = b4GapPatternWeight 5 4 5 * 0 :=
      b4GapContribution_from_row 1 5 4 5 0 row_01_05_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_04_05

theorem row_01_05_04_06 : b4RowContribution (![1, 6, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 10, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 10 + 16 = 33
    decide
  have hzsq : (∑ i, (((![1, 6, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 393 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 10^2 + 16^2 = 393
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_04_06

theorem weighted_01_05_04_06 : b4RawGapContribution ![1, 5, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 4, 6] = b4GapPatternWeight 5 4 6 * 0 :=
      b4GapContribution_from_row 1 5 4 6 0 row_01_05_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_04_06

theorem row_01_05_04_07 : b4RowContribution (![1, 6, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 10, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 10 + 17 = 34
    decide
  have hzsq : (∑ i, (((![1, 6, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 426 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 10^2 + 17^2 = 426
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_04_07

theorem weighted_01_05_04_07 : b4RawGapContribution ![1, 5, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 4, 7] = b4GapPatternWeight 5 4 7 * 0 :=
      b4GapContribution_from_row 1 5 4 7 0 row_01_05_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_04_07

theorem row_01_05_04_08 : b4RowContribution (![1, 6, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 10, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 10 + 18 = 35
    decide
  have hzsq : (∑ i, (((![1, 6, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 461 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 10^2 + 18^2 = 461
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_04_08

theorem weighted_01_05_04_08 : b4RawGapContribution ![1, 5, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 4, 8] = b4GapPatternWeight 5 4 8 * 0 :=
      b4GapContribution_from_row 1 5 4 8 0 row_01_05_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_04_08

theorem row_01_05_04_09 : b4RowContribution (![1, 6, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 10, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 10 + 19 = 36
    decide
  have hzsq : (∑ i, (((![1, 6, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 498 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 10^2 + 19^2 = 498
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_04_09

theorem weighted_01_05_04_09 : b4RawGapContribution ![1, 5, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 4, 9] = b4GapPatternWeight 5 4 9 * 0 :=
      b4GapContribution_from_row 1 5 4 9 0 row_01_05_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_04_09

theorem row_01_05_04_10 : b4RowContribution (![1, 6, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 10, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 10 + 20 = 37
    decide
  have hzsq : (∑ i, (((![1, 6, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 537 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 10^2 + 20^2 = 537
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_04_10

theorem weighted_01_05_04_10 : b4RawGapContribution ![1, 5, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 4, 10] = b4GapPatternWeight 5 4 10 * 0 :=
      b4GapContribution_from_row 1 5 4 10 0 row_01_05_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_04_10

def dvalues_01_05_04 : Fin 11 → ℕ := ![192, 0, 2064, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_05_04

theorem dblock_01_05_04 : b4GapPatternDBlock 1 5 4 = 2256 := by
  calc
    b4GapPatternDBlock 1 5 4 = ∑ d : Fin 11, dvalues_01_05_04 d := by
      apply b4GapDBlock_of_rows 1 5 4 dvalues_01_05_04
      intro d
      fin_cases d
      · exact weighted_01_05_04_00
      · exact weighted_01_05_04_01
      · exact weighted_01_05_04_02
      · exact weighted_01_05_04_03
      · exact weighted_01_05_04_04
      · exact weighted_01_05_04_05
      · exact weighted_01_05_04_06
      · exact weighted_01_05_04_07
      · exact weighted_01_05_04_08
      · exact weighted_01_05_04_09
      · exact weighted_01_05_04_10
    _ = 2256 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_05_04

end Paper7MomentGapNumeric
