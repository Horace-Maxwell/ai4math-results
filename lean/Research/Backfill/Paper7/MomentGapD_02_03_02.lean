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

theorem row_02_03_02_00 : b4RowContribution (![2, 5, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 7] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 7 = 21
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 127 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 7^2 = 127
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_00

theorem weighted_02_03_02_00 : b4RawGapContribution ![2, 3, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 0] = b4GapPatternWeight 3 2 0 * 0 :=
      b4GapContribution_from_row 2 3 2 0 0 row_02_03_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_00

theorem row_02_03_02_01 : b4RowContribution (![2, 5, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 8] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 8 = 22
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 142 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 8^2 = 142
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_01

theorem weighted_02_03_02_01 : b4RawGapContribution ![2, 3, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 1] = b4GapPatternWeight 3 2 1 * 0 :=
      b4GapContribution_from_row 2 3 2 1 0 row_02_03_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_01

theorem row_02_03_02_02 : b4RowContribution (![2, 5, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 9] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 9 = 23
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 159 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 9^2 = 159
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_02

theorem weighted_02_03_02_02 : b4RawGapContribution ![2, 3, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 2] = b4GapPatternWeight 3 2 2 * 0 :=
      b4GapContribution_from_row 2 3 2 2 0 row_02_03_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_02

theorem row_02_03_02_03 : b4RowContribution (![2, 5, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 10] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 10 = 24
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 178 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 10^2 = 178
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_03

theorem weighted_02_03_02_03 : b4RawGapContribution ![2, 3, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 3] = b4GapPatternWeight 3 2 3 * 0 :=
      b4GapContribution_from_row 2 3 2 3 0 row_02_03_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_03

theorem row_02_03_02_04 : b4RowContribution (![2, 5, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 11] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 11 = 25
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 199 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 11^2 = 199
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_04

theorem weighted_02_03_02_04 : b4RawGapContribution ![2, 3, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 4] = b4GapPatternWeight 3 2 4 * 0 :=
      b4GapContribution_from_row 2 3 2 4 0 row_02_03_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_04

theorem row_02_03_02_05 : b4RowContribution (![2, 5, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 12] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 12 = 26
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 222 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 12^2 = 222
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_05

theorem weighted_02_03_02_05 : b4RawGapContribution ![2, 3, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 5] = b4GapPatternWeight 3 2 5 * 0 :=
      b4GapContribution_from_row 2 3 2 5 0 row_02_03_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_05

theorem row_02_03_02_06 : b4RowContribution (![2, 5, 7, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 13 = 27
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 247 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 13^2 = 247
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_06

theorem weighted_02_03_02_06 : b4RawGapContribution ![2, 3, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 6] = b4GapPatternWeight 3 2 6 * 0 :=
      b4GapContribution_from_row 2 3 2 6 0 row_02_03_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_06

def layers_02_03_02_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 17, 18, 17, 15, 12, 9, 6, 3, 1, 0, 0, 0, 0], ![1, 4, 10, 19, 31, 46, 63, 81, 98, 113, 125, 134, 140, 143, 144, 143, 140, 134, 125]]
#print axioms Paper7MomentGapNumeric.layers_02_03_02_07

theorem cells_02_03_02_07 : QTableValid (![2, 5, 7, 14] : Fin 4 → ℕ) layers_02_03_02_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_03_02_07

theorem valid_02_03_02_07 :
    SparseRowValid (![2, 5, 7, 14] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_02_03_02_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 5, 7, 14] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 2 + 5 + 7 + 14 = 28
      decide
    have hzsq : (∑ i, (((![2, 5, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 274 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 5^2 + 7^2 + 14^2 = 274
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_03_02_07
#print axioms Paper7MomentGapNumeric.valid_02_03_02_07

def qvalues_02_03_02_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_03_02_07

theorem row_02_03_02_07 : b4RowContribution (![2, 5, 7, 14] : Fin 4 → ℕ) = 81 := by
  calc
    b4RowContribution (![2, 5, 7, 14] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_02_03_02_07) :=
      sparseRow_sound (![2, 5, 7, 14] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_02_03_02_07) valid_02_03_02_07
    _ = 81 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_03_02_07 Q := by
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
        _ = 81 := by decide
#print axioms Paper7MomentGapNumeric.row_02_03_02_07

theorem weighted_02_03_02_07 : b4RawGapContribution ![2, 3, 2, 7] = 1944 := by
  calc
    b4RawGapContribution ![2, 3, 2, 7] = b4GapPatternWeight 3 2 7 * 81 :=
      b4GapContribution_from_row 2 3 2 7 81 row_02_03_02_07
    _ = 1944 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_07

theorem row_02_03_02_08 : b4RowContribution (![2, 5, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 15 = 29
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 303 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 15^2 = 303
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_08

theorem weighted_02_03_02_08 : b4RawGapContribution ![2, 3, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 8] = b4GapPatternWeight 3 2 8 * 0 :=
      b4GapContribution_from_row 2 3 2 8 0 row_02_03_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_08

theorem row_02_03_02_09 : b4RowContribution (![2, 5, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 16 = 30
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 334 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 16^2 = 334
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_09

theorem weighted_02_03_02_09 : b4RawGapContribution ![2, 3, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 9] = b4GapPatternWeight 3 2 9 * 0 :=
      b4GapContribution_from_row 2 3 2 9 0 row_02_03_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_09

theorem row_02_03_02_10 : b4RowContribution (![2, 5, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 17 = 31
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 367 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 17^2 = 367
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_10

theorem weighted_02_03_02_10 : b4RawGapContribution ![2, 3, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 10] = b4GapPatternWeight 3 2 10 * 0 :=
      b4GapContribution_from_row 2 3 2 10 0 row_02_03_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_10

theorem row_02_03_02_11 : b4RowContribution (![2, 5, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 18 = 32
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 402 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 18^2 = 402
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_11

theorem weighted_02_03_02_11 : b4RawGapContribution ![2, 3, 2, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 11] = b4GapPatternWeight 3 2 11 * 0 :=
      b4GapContribution_from_row 2 3 2 11 0 row_02_03_02_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_11

theorem row_02_03_02_12 : b4RowContribution (![2, 5, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 19 = 33
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 439 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 19^2 = 439
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_12

theorem weighted_02_03_02_12 : b4RawGapContribution ![2, 3, 2, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 12] = b4GapPatternWeight 3 2 12 * 0 :=
      b4GapContribution_from_row 2 3 2 12 0 row_02_03_02_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_12

theorem row_02_03_02_13 : b4RowContribution (![2, 5, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 20 = 34
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 478 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 20^2 = 478
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_13

theorem weighted_02_03_02_13 : b4RawGapContribution ![2, 3, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 13] = b4GapPatternWeight 3 2 13 * 0 :=
      b4GapContribution_from_row 2 3 2 13 0 row_02_03_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_13

theorem row_02_03_02_14 : b4RowContribution (![2, 5, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 21 = 35
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 519 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 21^2 = 519
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_14

theorem weighted_02_03_02_14 : b4RawGapContribution ![2, 3, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 14] = b4GapPatternWeight 3 2 14 * 0 :=
      b4GapContribution_from_row 2 3 2 14 0 row_02_03_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_14

theorem row_02_03_02_15 : b4RowContribution (![2, 5, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 22 = 36
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 562 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 22^2 = 562
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_15

theorem weighted_02_03_02_15 : b4RawGapContribution ![2, 3, 2, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 15] = b4GapPatternWeight 3 2 15 * 0 :=
      b4GapContribution_from_row 2 3 2 15 0 row_02_03_02_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_15

theorem row_02_03_02_16 : b4RowContribution (![2, 5, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 7, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 7 + 23 = 37
    decide
  have hzsq : (∑ i, (((![2, 5, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 607 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 7^2 + 23^2 = 607
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_02_16

theorem weighted_02_03_02_16 : b4RawGapContribution ![2, 3, 2, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 2, 16] = b4GapPatternWeight 3 2 16 * 0 :=
      b4GapContribution_from_row 2 3 2 16 0 row_02_03_02_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_02_16

def dvalues_02_03_02 : Fin 17 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 1944, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_03_02

theorem dblock_02_03_02 : b4GapPatternDBlock 2 3 2 = 1944 := by
  calc
    b4GapPatternDBlock 2 3 2 = ∑ d : Fin 17, dvalues_02_03_02 d := by
      apply b4GapDBlock_of_rows 2 3 2 dvalues_02_03_02
      intro d
      fin_cases d
      · exact weighted_02_03_02_00
      · exact weighted_02_03_02_01
      · exact weighted_02_03_02_02
      · exact weighted_02_03_02_03
      · exact weighted_02_03_02_04
      · exact weighted_02_03_02_05
      · exact weighted_02_03_02_06
      · exact weighted_02_03_02_07
      · exact weighted_02_03_02_08
      · exact weighted_02_03_02_09
      · exact weighted_02_03_02_10
      · exact weighted_02_03_02_11
      · exact weighted_02_03_02_12
      · exact weighted_02_03_02_13
      · exact weighted_02_03_02_14
      · exact weighted_02_03_02_15
      · exact weighted_02_03_02_16
    _ = 1944 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_03_02

end Paper7MomentGapNumeric
