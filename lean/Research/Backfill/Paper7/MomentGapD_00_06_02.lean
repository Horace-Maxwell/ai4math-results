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

theorem row_00_06_02_00 : b4RowContribution (![0, 6, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 8] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 8 = 22
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 164 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 8^2 = 164
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_00

theorem weighted_00_06_02_00 : b4RawGapContribution ![0, 6, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 0] = b4GapPatternWeight 6 2 0 * 0 :=
      b4GapContribution_from_row 0 6 2 0 0 row_00_06_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_00

theorem row_00_06_02_01 : b4RowContribution (![0, 6, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 9] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 9 = 23
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 181 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 9^2 = 181
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_01

theorem weighted_00_06_02_01 : b4RawGapContribution ![0, 6, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 1] = b4GapPatternWeight 6 2 1 * 0 :=
      b4GapContribution_from_row 0 6 2 1 0 row_00_06_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_01

theorem row_00_06_02_02 : b4RowContribution (![0, 6, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 10] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 10 = 24
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 200 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 10^2 = 200
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_02

theorem weighted_00_06_02_02 : b4RawGapContribution ![0, 6, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 2] = b4GapPatternWeight 6 2 2 * 0 :=
      b4GapContribution_from_row 0 6 2 2 0 row_00_06_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_02

def layers_00_06_02_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 35, 42, 48, 53, 57, 59, 59, 57, 53, 48, 42, 35]]
#print axioms Paper7MomentGapNumeric.layers_00_06_02_03

theorem cells_00_06_02_03 : QTableValid (![0, 6, 8, 11] : Fin 4 → ℕ) layers_00_06_02_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_06_02_03

theorem valid_00_06_02_03 :
    SparseRowValid (![0, 6, 8, 11] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_06_02_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 6, 8, 11] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 6 + 8 + 11 = 25
      decide
    have hzsq : (∑ i, (((![0, 6, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 221 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 6^2 + 8^2 + 11^2 = 221
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_06_02_03
#print axioms Paper7MomentGapNumeric.valid_00_06_02_03

def qvalues_00_06_02_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_06_02_03

theorem row_00_06_02_03 : b4RowContribution (![0, 6, 8, 11] : Fin 4 → ℕ) = 42 := by
  calc
    b4RowContribution (![0, 6, 8, 11] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_00_06_02_03) :=
      sparseRow_sound (![0, 6, 8, 11] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_06_02_03) valid_00_06_02_03
    _ = 42 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_06_02_03 Q := by
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
        _ = 42 := by decide
#print axioms Paper7MomentGapNumeric.row_00_06_02_03

theorem weighted_00_06_02_03 : b4RawGapContribution ![0, 6, 2, 3] = 1008 := by
  calc
    b4RawGapContribution ![0, 6, 2, 3] = b4GapPatternWeight 6 2 3 * 42 :=
      b4GapContribution_from_row 0 6 2 3 42 row_00_06_02_03
    _ = 1008 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_03

theorem row_00_06_02_04 : b4RowContribution (![0, 6, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 12] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 12 = 26
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 244 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 12^2 = 244
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_04

theorem weighted_00_06_02_04 : b4RawGapContribution ![0, 6, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 4] = b4GapPatternWeight 6 2 4 * 0 :=
      b4GapContribution_from_row 0 6 2 4 0 row_00_06_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_04

theorem row_00_06_02_05 : b4RowContribution (![0, 6, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 13 = 27
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 269 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 13^2 = 269
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_05

theorem weighted_00_06_02_05 : b4RawGapContribution ![0, 6, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 5] = b4GapPatternWeight 6 2 5 * 0 :=
      b4GapContribution_from_row 0 6 2 5 0 row_00_06_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_05

theorem row_00_06_02_06 : b4RowContribution (![0, 6, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 14] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 14 = 28
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 296 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 14^2 = 296
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_06

theorem weighted_00_06_02_06 : b4RawGapContribution ![0, 6, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 6] = b4GapPatternWeight 6 2 6 * 0 :=
      b4GapContribution_from_row 0 6 2 6 0 row_00_06_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_06

theorem row_00_06_02_07 : b4RowContribution (![0, 6, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 15 = 29
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 15^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_07

theorem weighted_00_06_02_07 : b4RawGapContribution ![0, 6, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 7] = b4GapPatternWeight 6 2 7 * 0 :=
      b4GapContribution_from_row 0 6 2 7 0 row_00_06_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_07

theorem row_00_06_02_08 : b4RowContribution (![0, 6, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 16 = 30
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 356 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 16^2 = 356
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_08

theorem weighted_00_06_02_08 : b4RawGapContribution ![0, 6, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 8] = b4GapPatternWeight 6 2 8 * 0 :=
      b4GapContribution_from_row 0 6 2 8 0 row_00_06_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_08

theorem row_00_06_02_09 : b4RowContribution (![0, 6, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 17 = 31
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 389 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 17^2 = 389
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_09

theorem weighted_00_06_02_09 : b4RawGapContribution ![0, 6, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 9] = b4GapPatternWeight 6 2 9 * 0 :=
      b4GapContribution_from_row 0 6 2 9 0 row_00_06_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_09

theorem row_00_06_02_10 : b4RowContribution (![0, 6, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 18 = 32
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 424 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 18^2 = 424
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_10

theorem weighted_00_06_02_10 : b4RawGapContribution ![0, 6, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 10] = b4GapPatternWeight 6 2 10 * 0 :=
      b4GapContribution_from_row 0 6 2 10 0 row_00_06_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_10

theorem row_00_06_02_11 : b4RowContribution (![0, 6, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 19 = 33
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 461 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 19^2 = 461
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_11

theorem weighted_00_06_02_11 : b4RawGapContribution ![0, 6, 2, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 11] = b4GapPatternWeight 6 2 11 * 0 :=
      b4GapContribution_from_row 0 6 2 11 0 row_00_06_02_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_11

theorem row_00_06_02_12 : b4RowContribution (![0, 6, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 20 = 34
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 500 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 20^2 = 500
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_12

theorem weighted_00_06_02_12 : b4RawGapContribution ![0, 6, 2, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 12] = b4GapPatternWeight 6 2 12 * 0 :=
      b4GapContribution_from_row 0 6 2 12 0 row_00_06_02_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_12

theorem row_00_06_02_13 : b4RowContribution (![0, 6, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 21 = 35
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 541 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 21^2 = 541
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_13

theorem weighted_00_06_02_13 : b4RawGapContribution ![0, 6, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 13] = b4GapPatternWeight 6 2 13 * 0 :=
      b4GapContribution_from_row 0 6 2 13 0 row_00_06_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_13

theorem row_00_06_02_14 : b4RowContribution (![0, 6, 8, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 22 = 36
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 584 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 22^2 = 584
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_14

theorem weighted_00_06_02_14 : b4RawGapContribution ![0, 6, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 14] = b4GapPatternWeight 6 2 14 * 0 :=
      b4GapContribution_from_row 0 6 2 14 0 row_00_06_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_14

theorem row_00_06_02_15 : b4RowContribution (![0, 6, 8, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 8, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 8 + 23 = 37
    decide
  have hzsq : (∑ i, (((![0, 6, 8, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 629 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 8^2 + 23^2 = 629
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_02_15

theorem weighted_00_06_02_15 : b4RawGapContribution ![0, 6, 2, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 2, 15] = b4GapPatternWeight 6 2 15 * 0 :=
      b4GapContribution_from_row 0 6 2 15 0 row_00_06_02_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_02_15

def dvalues_00_06_02 : Fin 16 → ℕ := ![0, 0, 0, 1008, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_06_02

theorem dblock_00_06_02 : b4GapPatternDBlock 0 6 2 = 1008 := by
  calc
    b4GapPatternDBlock 0 6 2 = ∑ d : Fin 16, dvalues_00_06_02 d := by
      apply b4GapDBlock_of_rows 0 6 2 dvalues_00_06_02
      intro d
      fin_cases d
      · exact weighted_00_06_02_00
      · exact weighted_00_06_02_01
      · exact weighted_00_06_02_02
      · exact weighted_00_06_02_03
      · exact weighted_00_06_02_04
      · exact weighted_00_06_02_05
      · exact weighted_00_06_02_06
      · exact weighted_00_06_02_07
      · exact weighted_00_06_02_08
      · exact weighted_00_06_02_09
      · exact weighted_00_06_02_10
      · exact weighted_00_06_02_11
      · exact weighted_00_06_02_12
      · exact weighted_00_06_02_13
      · exact weighted_00_06_02_14
      · exact weighted_00_06_02_15
    _ = 1008 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_06_02

end Paper7MomentGapNumeric
