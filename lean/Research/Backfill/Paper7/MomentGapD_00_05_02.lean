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

theorem row_00_05_02_00 : b4RowContribution (![0, 5, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 7] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 7 = 19
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 123 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 7^2 = 123
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_00

theorem weighted_00_05_02_00 : b4RawGapContribution ![0, 5, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 0] = b4GapPatternWeight 5 2 0 * 0 :=
      b4GapContribution_from_row 0 5 2 0 0 row_00_05_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_00

theorem row_00_05_02_01 : b4RowContribution (![0, 5, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 8] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 8 = 20
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 138 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 8^2 = 138
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_01

theorem weighted_00_05_02_01 : b4RawGapContribution ![0, 5, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 1] = b4GapPatternWeight 5 2 1 * 0 :=
      b4GapContribution_from_row 0 5 2 1 0 row_00_05_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_01

theorem row_00_05_02_02 : b4RowContribution (![0, 5, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 9] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 9 = 21
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 155 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 9^2 = 155
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_02

theorem weighted_00_05_02_02 : b4RawGapContribution ![0, 5, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 2] = b4GapPatternWeight 5 2 2 * 0 :=
      b4GapContribution_from_row 0 5 2 2 0 row_00_05_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_02

theorem row_00_05_02_03 : b4RowContribution (![0, 5, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 10] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 10 = 22
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 174 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 10^2 = 174
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_03

theorem weighted_00_05_02_03 : b4RawGapContribution ![0, 5, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 3] = b4GapPatternWeight 5 2 3 * 0 :=
      b4GapContribution_from_row 0 5 2 3 0 row_00_05_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_03

theorem row_00_05_02_04 : b4RowContribution (![0, 5, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 11] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 11 = 23
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 195 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 11^2 = 195
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_04

theorem weighted_00_05_02_04 : b4RawGapContribution ![0, 5, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 4] = b4GapPatternWeight 5 2 4 * 0 :=
      b4GapContribution_from_row 0 5 2 4 0 row_00_05_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_04

def layers_00_05_02_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 27, 33, 38, 42, 45, 47, 48, 47, 45, 42, 38, 33, 27]]
#print axioms Paper7MomentGapNumeric.layers_00_05_02_05

theorem cells_00_05_02_05 : QTableValid (![0, 5, 7, 12] : Fin 4 → ℕ) layers_00_05_02_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_05_02_05

theorem valid_00_05_02_05 :
    SparseRowValid (![0, 5, 7, 12] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_05_02_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 5, 7, 12] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 0 + 5 + 7 + 12 = 24
      decide
    have hzsq : (∑ i, (((![0, 5, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 218 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 5^2 + 7^2 + 12^2 = 218
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_05_02_05
#print axioms Paper7MomentGapNumeric.valid_00_05_02_05

def qvalues_00_05_02_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_05_02_05

theorem row_00_05_02_05 : b4RowContribution (![0, 5, 7, 12] : Fin 4 → ℕ) = 47 := by
  calc
    b4RowContribution (![0, 5, 7, 12] : Fin 4 → ℕ) =
        sparseRowValue ({11} : Finset (Fin 19)) (fun _ => layers_00_05_02_05) :=
      sparseRow_sound (![0, 5, 7, 12] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_05_02_05) valid_00_05_02_05
    _ = 47 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_05_02_05 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 47 := by decide
#print axioms Paper7MomentGapNumeric.row_00_05_02_05

theorem weighted_00_05_02_05 : b4RawGapContribution ![0, 5, 2, 5] = 1128 := by
  calc
    b4RawGapContribution ![0, 5, 2, 5] = b4GapPatternWeight 5 2 5 * 47 :=
      b4GapContribution_from_row 0 5 2 5 47 row_00_05_02_05
    _ = 1128 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_05

theorem row_00_05_02_06 : b4RowContribution (![0, 5, 7, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 13] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 13 = 25
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 243 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 13^2 = 243
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_06

theorem weighted_00_05_02_06 : b4RawGapContribution ![0, 5, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 6] = b4GapPatternWeight 5 2 6 * 0 :=
      b4GapContribution_from_row 0 5 2 6 0 row_00_05_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_06

theorem row_00_05_02_07 : b4RowContribution (![0, 5, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 14] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 14 = 26
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 14^2 = 270
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_07

theorem weighted_00_05_02_07 : b4RawGapContribution ![0, 5, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 7] = b4GapPatternWeight 5 2 7 * 0 :=
      b4GapContribution_from_row 0 5 2 7 0 row_00_05_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_07

theorem row_00_05_02_08 : b4RowContribution (![0, 5, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 15] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 15 = 27
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 299 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 15^2 = 299
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_08

theorem weighted_00_05_02_08 : b4RawGapContribution ![0, 5, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 8] = b4GapPatternWeight 5 2 8 * 0 :=
      b4GapContribution_from_row 0 5 2 8 0 row_00_05_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_08

theorem row_00_05_02_09 : b4RowContribution (![0, 5, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 16] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 16 = 28
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 330 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 16^2 = 330
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_09

theorem weighted_00_05_02_09 : b4RawGapContribution ![0, 5, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 9] = b4GapPatternWeight 5 2 9 * 0 :=
      b4GapContribution_from_row 0 5 2 9 0 row_00_05_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_09

theorem row_00_05_02_10 : b4RowContribution (![0, 5, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 17] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 17 = 29
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 363 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 17^2 = 363
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_10

theorem weighted_00_05_02_10 : b4RawGapContribution ![0, 5, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 10] = b4GapPatternWeight 5 2 10 * 0 :=
      b4GapContribution_from_row 0 5 2 10 0 row_00_05_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_10

theorem row_00_05_02_11 : b4RowContribution (![0, 5, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 18] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 18 = 30
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 398 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 18^2 = 398
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_11

theorem weighted_00_05_02_11 : b4RawGapContribution ![0, 5, 2, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 11] = b4GapPatternWeight 5 2 11 * 0 :=
      b4GapContribution_from_row 0 5 2 11 0 row_00_05_02_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_11

theorem row_00_05_02_12 : b4RowContribution (![0, 5, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 19] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 19 = 31
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 435 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 19^2 = 435
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_12

theorem weighted_00_05_02_12 : b4RawGapContribution ![0, 5, 2, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 12] = b4GapPatternWeight 5 2 12 * 0 :=
      b4GapContribution_from_row 0 5 2 12 0 row_00_05_02_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_12

theorem row_00_05_02_13 : b4RowContribution (![0, 5, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 20] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 20 = 32
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 474 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 20^2 = 474
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_13

theorem weighted_00_05_02_13 : b4RawGapContribution ![0, 5, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 13] = b4GapPatternWeight 5 2 13 * 0 :=
      b4GapContribution_from_row 0 5 2 13 0 row_00_05_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_13

theorem row_00_05_02_14 : b4RowContribution (![0, 5, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 21] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 21 = 33
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 515 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 21^2 = 515
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_14

theorem weighted_00_05_02_14 : b4RawGapContribution ![0, 5, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 14] = b4GapPatternWeight 5 2 14 * 0 :=
      b4GapContribution_from_row 0 5 2 14 0 row_00_05_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_14

theorem row_00_05_02_15 : b4RowContribution (![0, 5, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 22] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 22 = 34
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 558 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 22^2 = 558
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_15

theorem weighted_00_05_02_15 : b4RawGapContribution ![0, 5, 2, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 15] = b4GapPatternWeight 5 2 15 * 0 :=
      b4GapContribution_from_row 0 5 2 15 0 row_00_05_02_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_15

theorem row_00_05_02_16 : b4RowContribution (![0, 5, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 23] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 23 = 35
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 603 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 23^2 = 603
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_16

theorem weighted_00_05_02_16 : b4RawGapContribution ![0, 5, 2, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 16] = b4GapPatternWeight 5 2 16 * 0 :=
      b4GapContribution_from_row 0 5 2 16 0 row_00_05_02_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_16

theorem row_00_05_02_17 : b4RowContribution (![0, 5, 7, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 24] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 24 = 36
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 650 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 24^2 = 650
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_17

theorem weighted_00_05_02_17 : b4RawGapContribution ![0, 5, 2, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 17] = b4GapPatternWeight 5 2 17 * 0 :=
      b4GapContribution_from_row 0 5 2 17 0 row_00_05_02_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_17

theorem row_00_05_02_18 : b4RowContribution (![0, 5, 7, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 7, 25] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 7 + 25 = 37
    decide
  have hzsq : (∑ i, (((![0, 5, 7, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 699 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 7^2 + 25^2 = 699
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_02_18

theorem weighted_00_05_02_18 : b4RawGapContribution ![0, 5, 2, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 2, 18] = b4GapPatternWeight 5 2 18 * 0 :=
      b4GapContribution_from_row 0 5 2 18 0 row_00_05_02_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_02_18

def dvalues_00_05_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 1128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_05_02

theorem dblock_00_05_02 : b4GapPatternDBlock 0 5 2 = 1128 := by
  calc
    b4GapPatternDBlock 0 5 2 = ∑ d : Fin 19, dvalues_00_05_02 d := by
      apply b4GapDBlock_of_rows 0 5 2 dvalues_00_05_02
      intro d
      fin_cases d
      · exact weighted_00_05_02_00
      · exact weighted_00_05_02_01
      · exact weighted_00_05_02_02
      · exact weighted_00_05_02_03
      · exact weighted_00_05_02_04
      · exact weighted_00_05_02_05
      · exact weighted_00_05_02_06
      · exact weighted_00_05_02_07
      · exact weighted_00_05_02_08
      · exact weighted_00_05_02_09
      · exact weighted_00_05_02_10
      · exact weighted_00_05_02_11
      · exact weighted_00_05_02_12
      · exact weighted_00_05_02_13
      · exact weighted_00_05_02_14
      · exact weighted_00_05_02_15
      · exact weighted_00_05_02_16
      · exact weighted_00_05_02_17
      · exact weighted_00_05_02_18
    _ = 1128 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_05_02

end Paper7MomentGapNumeric
