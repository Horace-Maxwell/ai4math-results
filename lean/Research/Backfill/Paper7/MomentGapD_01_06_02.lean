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

theorem row_01_06_02_00 : b4RowContribution (![1, 7, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 9, 9] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 9 + 9 = 26
    decide
  have hzsq : (∑ i, (((![1, 7, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 212 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 9^2 + 9^2 = 212
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_02_00

theorem weighted_01_06_02_00 : b4RawGapContribution ![1, 6, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 2, 0] = b4GapPatternWeight 6 2 0 * 0 :=
      b4GapContribution_from_row 1 6 2 0 0 row_01_06_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_02_00

def layers_01_06_02_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 16, 16, 15, 13, 11, 9, 7, 5, 3, 1, 0], ![1, 4, 9, 16, 25, 36, 49, 64, 80, 96, 111, 123, 131, 135, 135, 131, 123, 111, 96]]
#print axioms Paper7MomentGapNumeric.layers_01_06_02_01

theorem cells_01_06_02_01 : QTableValid (![1, 7, 9, 10] : Fin 4 → ℕ) layers_01_06_02_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_06_02_01

theorem valid_01_06_02_01 :
    SparseRowValid (![1, 7, 9, 10] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_06_02_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 7, 9, 10] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 1 + 7 + 9 + 10 = 27
      decide
    have hzsq : (∑ i, (((![1, 7, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 231 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 7^2 + 9^2 + 10^2 = 231
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_06_02_01
#print axioms Paper7MomentGapNumeric.valid_01_06_02_01

def qvalues_01_06_02_01 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_06_02_01

theorem row_01_06_02_01 : b4RowContribution (![1, 7, 9, 10] : Fin 4 → ℕ) = 50 := by
  calc
    b4RowContribution (![1, 7, 9, 10] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_06_02_01) :=
      sparseRow_sound (![1, 7, 9, 10] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_06_02_01) valid_01_06_02_01
    _ = 50 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_06_02_01 Q := by
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
        _ = 50 := by decide
#print axioms Paper7MomentGapNumeric.row_01_06_02_01

theorem weighted_01_06_02_01 : b4RawGapContribution ![1, 6, 2, 1] = 1200 := by
  calc
    b4RawGapContribution ![1, 6, 2, 1] = b4GapPatternWeight 6 2 1 * 50 :=
      b4GapContribution_from_row 1 6 2 1 50 row_01_06_02_01
    _ = 1200 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_02_01

theorem row_01_06_02_02 : b4RowContribution (![1, 7, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 9, 11] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 9 + 11 = 28
    decide
  have hzsq : (∑ i, (((![1, 7, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 252 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 9^2 + 11^2 = 252
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_02_02

theorem weighted_01_06_02_02 : b4RawGapContribution ![1, 6, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 2, 2] = b4GapPatternWeight 6 2 2 * 0 :=
      b4GapContribution_from_row 1 6 2 2 0 row_01_06_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_02_02

def layers_01_06_02_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 16, 16, 15, 13, 11, 9, 7, 5, 3, 1, 0], ![1, 4, 9, 16, 25, 36, 49, 64, 80, 96, 111, 124, 135, 143, 147, 147, 143, 135, 124]]
#print axioms Paper7MomentGapNumeric.layers_01_06_02_03

theorem cells_01_06_02_03 : QTableValid (![1, 7, 9, 12] : Fin 4 → ℕ) layers_01_06_02_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_06_02_03

theorem valid_01_06_02_03 :
    SparseRowValid (![1, 7, 9, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_01_06_02_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 7, 9, 12] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 1 + 7 + 9 + 12 = 29
      decide
    have hzsq : (∑ i, (((![1, 7, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 275 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 7^2 + 9^2 + 12^2 = 275
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_06_02_03
#print axioms Paper7MomentGapNumeric.valid_01_06_02_03

def qvalues_01_06_02_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_06_02_03

theorem row_01_06_02_03 : b4RowContribution (![1, 7, 9, 12] : Fin 4 → ℕ) = 36 := by
  calc
    b4RowContribution (![1, 7, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_01_06_02_03) :=
      sparseRow_sound (![1, 7, 9, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_01_06_02_03) valid_01_06_02_03
    _ = 36 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_06_02_03 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.row_01_06_02_03

theorem weighted_01_06_02_03 : b4RawGapContribution ![1, 6, 2, 3] = 864 := by
  calc
    b4RawGapContribution ![1, 6, 2, 3] = b4GapPatternWeight 6 2 3 * 36 :=
      b4GapContribution_from_row 1 6 2 3 36 row_01_06_02_03
    _ = 864 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_02_03

theorem row_01_06_02_04 : b4RowContribution (![1, 7, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 9, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 9 + 13 = 30
    decide
  have hzsq : (∑ i, (((![1, 7, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 300 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 9^2 + 13^2 = 300
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_02_04

theorem weighted_01_06_02_04 : b4RawGapContribution ![1, 6, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 2, 4] = b4GapPatternWeight 6 2 4 * 0 :=
      b4GapContribution_from_row 1 6 2 4 0 row_01_06_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_02_04

theorem row_01_06_02_05 : b4RowContribution (![1, 7, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 9, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 9 + 14 = 31
    decide
  have hzsq : (∑ i, (((![1, 7, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 327 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 9^2 + 14^2 = 327
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_02_05

theorem weighted_01_06_02_05 : b4RawGapContribution ![1, 6, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 2, 5] = b4GapPatternWeight 6 2 5 * 0 :=
      b4GapContribution_from_row 1 6 2 5 0 row_01_06_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_02_05

theorem row_01_06_02_06 : b4RowContribution (![1, 7, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 9, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 9 + 15 = 32
    decide
  have hzsq : (∑ i, (((![1, 7, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 356 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 9^2 + 15^2 = 356
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_02_06

theorem weighted_01_06_02_06 : b4RawGapContribution ![1, 6, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 2, 6] = b4GapPatternWeight 6 2 6 * 0 :=
      b4GapContribution_from_row 1 6 2 6 0 row_01_06_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_02_06

theorem row_01_06_02_07 : b4RowContribution (![1, 7, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 9, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 9 + 16 = 33
    decide
  have hzsq : (∑ i, (((![1, 7, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 387 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 9^2 + 16^2 = 387
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_02_07

theorem weighted_01_06_02_07 : b4RawGapContribution ![1, 6, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 2, 7] = b4GapPatternWeight 6 2 7 * 0 :=
      b4GapContribution_from_row 1 6 2 7 0 row_01_06_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_02_07

theorem row_01_06_02_08 : b4RowContribution (![1, 7, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 9, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 9 + 17 = 34
    decide
  have hzsq : (∑ i, (((![1, 7, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 420 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 9^2 + 17^2 = 420
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_02_08

theorem weighted_01_06_02_08 : b4RawGapContribution ![1, 6, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 2, 8] = b4GapPatternWeight 6 2 8 * 0 :=
      b4GapContribution_from_row 1 6 2 8 0 row_01_06_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_02_08

theorem row_01_06_02_09 : b4RowContribution (![1, 7, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 9, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 9 + 18 = 35
    decide
  have hzsq : (∑ i, (((![1, 7, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 455 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 9^2 + 18^2 = 455
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_02_09

theorem weighted_01_06_02_09 : b4RawGapContribution ![1, 6, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 2, 9] = b4GapPatternWeight 6 2 9 * 0 :=
      b4GapContribution_from_row 1 6 2 9 0 row_01_06_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_02_09

theorem row_01_06_02_10 : b4RowContribution (![1, 7, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 9, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 9 + 19 = 36
    decide
  have hzsq : (∑ i, (((![1, 7, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 492 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 9^2 + 19^2 = 492
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_02_10

theorem weighted_01_06_02_10 : b4RawGapContribution ![1, 6, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 2, 10] = b4GapPatternWeight 6 2 10 * 0 :=
      b4GapContribution_from_row 1 6 2 10 0 row_01_06_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_02_10

theorem row_01_06_02_11 : b4RowContribution (![1, 7, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 9, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 9 + 20 = 37
    decide
  have hzsq : (∑ i, (((![1, 7, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 531 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 9^2 + 20^2 = 531
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_02_11

theorem weighted_01_06_02_11 : b4RawGapContribution ![1, 6, 2, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 2, 11] = b4GapPatternWeight 6 2 11 * 0 :=
      b4GapContribution_from_row 1 6 2 11 0 row_01_06_02_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_02_11

def dvalues_01_06_02 : Fin 12 → ℕ := ![0, 1200, 0, 864, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_06_02

theorem dblock_01_06_02 : b4GapPatternDBlock 1 6 2 = 2064 := by
  calc
    b4GapPatternDBlock 1 6 2 = ∑ d : Fin 12, dvalues_01_06_02 d := by
      apply b4GapDBlock_of_rows 1 6 2 dvalues_01_06_02
      intro d
      fin_cases d
      · exact weighted_01_06_02_00
      · exact weighted_01_06_02_01
      · exact weighted_01_06_02_02
      · exact weighted_01_06_02_03
      · exact weighted_01_06_02_04
      · exact weighted_01_06_02_05
      · exact weighted_01_06_02_06
      · exact weighted_01_06_02_07
      · exact weighted_01_06_02_08
      · exact weighted_01_06_02_09
      · exact weighted_01_06_02_10
      · exact weighted_01_06_02_11
    _ = 2064 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_06_02

end Paper7MomentGapNumeric
