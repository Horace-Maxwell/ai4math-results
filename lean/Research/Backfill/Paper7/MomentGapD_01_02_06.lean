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

theorem row_01_02_06_00 : b4RowContribution (![1, 3, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 9, 9] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 9 + 9 = 22
    decide
  have hzsq : (∑ i, (((![1, 3, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 172 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 9^2 + 9^2 = 172
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_06_00

theorem weighted_01_02_06_00 : b4RawGapContribution ![1, 2, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 6, 0] = b4GapPatternWeight 2 6 0 * 0 :=
      b4GapContribution_from_row 1 2 6 0 0 row_01_02_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_00

theorem row_01_02_06_01 : b4RowContribution (![1, 3, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 9, 10] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 9 + 10 = 23
    decide
  have hzsq : (∑ i, (((![1, 3, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 191 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 9^2 + 10^2 = 191
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_06_01

theorem weighted_01_02_06_01 : b4RawGapContribution ![1, 2, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 6, 1] = b4GapPatternWeight 2 6 1 * 0 :=
      b4GapContribution_from_row 1 2 6 1 0 row_01_02_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_01

theorem row_01_02_06_02 : b4RowContribution (![1, 3, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 9, 11] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 9 + 11 = 24
    decide
  have hzsq : (∑ i, (((![1, 3, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 212 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 9^2 + 11^2 = 212
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_06_02

theorem weighted_01_02_06_02 : b4RawGapContribution ![1, 2, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 6, 2] = b4GapPatternWeight 2 6 2 * 0 :=
      b4GapContribution_from_row 1 2 6 2 0 row_01_02_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_02

def layers_01_02_06_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 8, 8, 8, 8, 8, 7, 5, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 32, 40, 48, 56, 64, 71, 76, 79, 79, 76, 71, 64, 56, 48]]
#print axioms Paper7MomentGapNumeric.layers_01_02_06_03

theorem cells_01_02_06_03 : QTableValid (![1, 3, 9, 12] : Fin 4 → ℕ) layers_01_02_06_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_06_03

theorem valid_01_02_06_03 :
    SparseRowValid (![1, 3, 9, 12] : Fin 4 → ℕ) ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_02_06_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 9, 12] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 9 + 12 = 25
      decide
    have hzsq : (∑ i, (((![1, 3, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 235 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 9^2 + 12^2 = 235
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_06_03
#print axioms Paper7MomentGapNumeric.valid_01_02_06_03

def qvalues_01_02_06_03 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_06_03

theorem row_01_02_06_03 : b4RowContribution (![1, 3, 9, 12] : Fin 4 → ℕ) = 52 := by
  calc
    b4RowContribution (![1, 3, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_02_06_03) :=
      sparseRow_sound (![1, 3, 9, 12] : Fin 4 → ℕ) ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_02_06_03) valid_01_02_06_03
    _ = 52 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_06_03 Q := by
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
        _ = 52 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_06_03

theorem weighted_01_02_06_03 : b4RawGapContribution ![1, 2, 6, 3] = 1248 := by
  calc
    b4RawGapContribution ![1, 2, 6, 3] = b4GapPatternWeight 2 6 3 * 52 :=
      b4GapContribution_from_row 1 2 6 3 52 row_01_02_06_03
    _ = 1248 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_03

theorem row_01_02_06_04 : b4RowContribution (![1, 3, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 9, 13] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 9 + 13 = 26
    decide
  have hzsq : (∑ i, (((![1, 3, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 260 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 9^2 + 13^2 = 260
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_06_04

theorem weighted_01_02_06_04 : b4RawGapContribution ![1, 2, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 6, 4] = b4GapPatternWeight 2 6 4 * 0 :=
      b4GapContribution_from_row 1 2 6 4 0 row_01_02_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_04

def layers_01_02_06_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 8, 8, 8, 8, 8, 7, 5, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 32, 40, 48, 56, 64, 71, 76, 79, 80, 80, 79, 76, 71, 64]]
#print axioms Paper7MomentGapNumeric.layers_01_02_06_05

theorem cells_01_02_06_05 : QTableValid (![1, 3, 9, 14] : Fin 4 → ℕ) layers_01_02_06_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_06_05

theorem valid_01_02_06_05 :
    SparseRowValid (![1, 3, 9, 14] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_01_02_06_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 9, 14] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 9 + 14 = 27
      decide
    have hzsq : (∑ i, (((![1, 3, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 287 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 9^2 + 14^2 = 287
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_06_05
#print axioms Paper7MomentGapNumeric.valid_01_02_06_05

def qvalues_01_02_06_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_06_05

theorem row_01_02_06_05 : b4RowContribution (![1, 3, 9, 14] : Fin 4 → ℕ) = 56 := by
  calc
    b4RowContribution (![1, 3, 9, 14] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_01_02_06_05) :=
      sparseRow_sound (![1, 3, 9, 14] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_01_02_06_05) valid_01_02_06_05
    _ = 56 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_06_05 Q := by
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
        _ = 56 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_06_05

theorem weighted_01_02_06_05 : b4RawGapContribution ![1, 2, 6, 5] = 1344 := by
  calc
    b4RawGapContribution ![1, 2, 6, 5] = b4GapPatternWeight 2 6 5 * 56 :=
      b4GapContribution_from_row 1 2 6 5 56 row_01_02_06_05
    _ = 1344 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_05

theorem row_01_02_06_06 : b4RowContribution (![1, 3, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 9, 15] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 9 + 15 = 28
    decide
  have hzsq : (∑ i, (((![1, 3, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 316 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 9^2 + 15^2 = 316
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_06_06

theorem weighted_01_02_06_06 : b4RawGapContribution ![1, 2, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 6, 6] = b4GapPatternWeight 2 6 6 * 0 :=
      b4GapContribution_from_row 1 2 6 6 0 row_01_02_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_06

theorem row_01_02_06_07 : b4RowContribution (![1, 3, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 9, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 9 + 16 = 29
    decide
  have hzsq : (∑ i, (((![1, 3, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 347 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 9^2 + 16^2 = 347
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_06_07

theorem weighted_01_02_06_07 : b4RawGapContribution ![1, 2, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 6, 7] = b4GapPatternWeight 2 6 7 * 0 :=
      b4GapContribution_from_row 1 2 6 7 0 row_01_02_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_07

theorem row_01_02_06_08 : b4RowContribution (![1, 3, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 9, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 9 + 17 = 30
    decide
  have hzsq : (∑ i, (((![1, 3, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 380 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 9^2 + 17^2 = 380
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_06_08

theorem weighted_01_02_06_08 : b4RawGapContribution ![1, 2, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 6, 8] = b4GapPatternWeight 2 6 8 * 0 :=
      b4GapContribution_from_row 1 2 6 8 0 row_01_02_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_08

theorem row_01_02_06_09 : b4RowContribution (![1, 3, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 9, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 9 + 18 = 31
    decide
  have hzsq : (∑ i, (((![1, 3, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 415 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 9^2 + 18^2 = 415
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_06_09

theorem weighted_01_02_06_09 : b4RawGapContribution ![1, 2, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 6, 9] = b4GapPatternWeight 2 6 9 * 0 :=
      b4GapContribution_from_row 1 2 6 9 0 row_01_02_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_09

theorem row_01_02_06_10 : b4RowContribution (![1, 3, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 9, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 9 + 19 = 32
    decide
  have hzsq : (∑ i, (((![1, 3, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 452 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 9^2 + 19^2 = 452
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_06_10

theorem weighted_01_02_06_10 : b4RawGapContribution ![1, 2, 6, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 6, 10] = b4GapPatternWeight 2 6 10 * 0 :=
      b4GapContribution_from_row 1 2 6 10 0 row_01_02_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_10

theorem row_01_02_06_11 : b4RowContribution (![1, 3, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 9, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 9 + 20 = 33
    decide
  have hzsq : (∑ i, (((![1, 3, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 491 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 9^2 + 20^2 = 491
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_06_11

theorem weighted_01_02_06_11 : b4RawGapContribution ![1, 2, 6, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 6, 11] = b4GapPatternWeight 2 6 11 * 0 :=
      b4GapContribution_from_row 1 2 6 11 0 row_01_02_06_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_11

theorem row_01_02_06_12 : b4RowContribution (![1, 3, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 9, 21] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 9 + 21 = 34
    decide
  have hzsq : (∑ i, (((![1, 3, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 532 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 9^2 + 21^2 = 532
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_06_12

theorem weighted_01_02_06_12 : b4RawGapContribution ![1, 2, 6, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 6, 12] = b4GapPatternWeight 2 6 12 * 0 :=
      b4GapContribution_from_row 1 2 6 12 0 row_01_02_06_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_12

theorem row_01_02_06_13 : b4RowContribution (![1, 3, 9, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 9, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 9 + 22 = 35
    decide
  have hzsq : (∑ i, (((![1, 3, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 575 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 9^2 + 22^2 = 575
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_06_13

theorem weighted_01_02_06_13 : b4RawGapContribution ![1, 2, 6, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 6, 13] = b4GapPatternWeight 2 6 13 * 0 :=
      b4GapContribution_from_row 1 2 6 13 0 row_01_02_06_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_13

theorem row_01_02_06_14 : b4RowContribution (![1, 3, 9, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 9, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 9 + 23 = 36
    decide
  have hzsq : (∑ i, (((![1, 3, 9, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 620 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 9^2 + 23^2 = 620
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_06_14

theorem weighted_01_02_06_14 : b4RawGapContribution ![1, 2, 6, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 6, 14] = b4GapPatternWeight 2 6 14 * 0 :=
      b4GapContribution_from_row 1 2 6 14 0 row_01_02_06_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_14

theorem row_01_02_06_15 : b4RowContribution (![1, 3, 9, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 9, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 9 + 24 = 37
    decide
  have hzsq : (∑ i, (((![1, 3, 9, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 667 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 9^2 + 24^2 = 667
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_06_15

theorem weighted_01_02_06_15 : b4RawGapContribution ![1, 2, 6, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 6, 15] = b4GapPatternWeight 2 6 15 * 0 :=
      b4GapContribution_from_row 1 2 6 15 0 row_01_02_06_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_06_15

def dvalues_01_02_06 : Fin 16 → ℕ := ![0, 0, 0, 1248, 0, 1344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_02_06

theorem dblock_01_02_06 : b4GapPatternDBlock 1 2 6 = 2592 := by
  calc
    b4GapPatternDBlock 1 2 6 = ∑ d : Fin 16, dvalues_01_02_06 d := by
      apply b4GapDBlock_of_rows 1 2 6 dvalues_01_02_06
      intro d
      fin_cases d
      · exact weighted_01_02_06_00
      · exact weighted_01_02_06_01
      · exact weighted_01_02_06_02
      · exact weighted_01_02_06_03
      · exact weighted_01_02_06_04
      · exact weighted_01_02_06_05
      · exact weighted_01_02_06_06
      · exact weighted_01_02_06_07
      · exact weighted_01_02_06_08
      · exact weighted_01_02_06_09
      · exact weighted_01_02_06_10
      · exact weighted_01_02_06_11
      · exact weighted_01_02_06_12
      · exact weighted_01_02_06_13
      · exact weighted_01_02_06_14
      · exact weighted_01_02_06_15
    _ = 2592 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_02_06

end Paper7MomentGapNumeric
