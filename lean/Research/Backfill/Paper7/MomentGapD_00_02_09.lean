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

theorem row_00_02_09_00 : b4RowContribution (![0, 2, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 11, 11] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 11 + 11 = 24
    decide
  have hzsq : (∑ i, (((![0, 2, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 246 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 11^2 + 11^2 = 246
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_09_00

theorem weighted_00_02_09_00 : b4RawGapContribution ![0, 2, 9, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 9, 0] = b4GapPatternWeight 2 9 0 * 0 :=
      b4GapContribution_from_row 0 2 9 0 0 row_00_02_09_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_09_00

theorem row_00_02_09_01 : b4RowContribution (![0, 2, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 11, 12] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 11 + 12 = 25
    decide
  have hzsq : (∑ i, (((![0, 2, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 269 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 11^2 + 12^2 = 269
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_09_01

theorem weighted_00_02_09_01 : b4RawGapContribution ![0, 2, 9, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 9, 1] = b4GapPatternWeight 2 9 1 * 0 :=
      b4GapContribution_from_row 0 2 9 1 0 row_00_02_09_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_09_01

theorem row_00_02_09_02 : b4RowContribution (![0, 2, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 11, 13] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 11 + 13 = 26
    decide
  have hzsq : (∑ i, (((![0, 2, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 294 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 11^2 + 13^2 = 294
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_09_02

theorem weighted_00_02_09_02 : b4RawGapContribution ![0, 2, 9, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 9, 2] = b4GapPatternWeight 2 9 2 * 0 :=
      b4GapContribution_from_row 0 2 9 2 0 row_00_02_09_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_09_02

theorem row_00_02_09_03 : b4RowContribution (![0, 2, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 11, 14] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 11 + 14 = 27
    decide
  have hzsq : (∑ i, (((![0, 2, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 321 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 11^2 + 14^2 = 321
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_09_03

theorem weighted_00_02_09_03 : b4RawGapContribution ![0, 2, 9, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 9, 3] = b4GapPatternWeight 2 9 3 * 0 :=
      b4GapContribution_from_row 0 2 9 3 0 row_00_02_09_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_09_03

theorem row_00_02_09_04 : b4RowContribution (![0, 2, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 11, 15] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 11 + 15 = 28
    decide
  have hzsq : (∑ i, (((![0, 2, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 350 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 11^2 + 15^2 = 350
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_09_04

theorem weighted_00_02_09_04 : b4RawGapContribution ![0, 2, 9, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 9, 4] = b4GapPatternWeight 2 9 4 * 0 :=
      b4GapContribution_from_row 0 2 9 4 0 row_00_02_09_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_09_04

theorem row_00_02_09_05 : b4RowContribution (![0, 2, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 11, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 11 + 16 = 29
    decide
  have hzsq : (∑ i, (((![0, 2, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 381 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 11^2 + 16^2 = 381
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_09_05

theorem weighted_00_02_09_05 : b4RawGapContribution ![0, 2, 9, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 9, 5] = b4GapPatternWeight 2 9 5 * 0 :=
      b4GapContribution_from_row 0 2 9 5 0 row_00_02_09_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_09_05

theorem row_00_02_09_06 : b4RowContribution (![0, 2, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 11, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 11 + 17 = 30
    decide
  have hzsq : (∑ i, (((![0, 2, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 414 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 11^2 + 17^2 = 414
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_09_06

theorem weighted_00_02_09_06 : b4RawGapContribution ![0, 2, 9, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 9, 6] = b4GapPatternWeight 2 9 6 * 0 :=
      b4GapContribution_from_row 0 2 9 6 0 row_00_02_09_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_09_06

theorem row_00_02_09_07 : b4RowContribution (![0, 2, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 11, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 11 + 18 = 31
    decide
  have hzsq : (∑ i, (((![0, 2, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 449 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 11^2 + 18^2 = 449
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_09_07

theorem weighted_00_02_09_07 : b4RawGapContribution ![0, 2, 9, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 9, 7] = b4GapPatternWeight 2 9 7 * 0 :=
      b4GapContribution_from_row 0 2 9 7 0 row_00_02_09_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_09_07

theorem row_00_02_09_08 : b4RowContribution (![0, 2, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 11, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 11 + 19 = 32
    decide
  have hzsq : (∑ i, (((![0, 2, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 486 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 11^2 + 19^2 = 486
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_09_08

theorem weighted_00_02_09_08 : b4RawGapContribution ![0, 2, 9, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 9, 8] = b4GapPatternWeight 2 9 8 * 0 :=
      b4GapContribution_from_row 0 2 9 8 0 row_00_02_09_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_09_08

theorem row_00_02_09_09 : b4RowContribution (![0, 2, 11, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 11, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 11 + 20 = 33
    decide
  have hzsq : (∑ i, (((![0, 2, 11, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 525 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 11^2 + 20^2 = 525
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_09_09

theorem weighted_00_02_09_09 : b4RawGapContribution ![0, 2, 9, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 9, 9] = b4GapPatternWeight 2 9 9 * 0 :=
      b4GapContribution_from_row 0 2 9 9 0 row_00_02_09_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_09_09

def layers_00_02_09_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 35, 36, 36, 36, 36, 36, 36]]
#print axioms Paper7MomentGapNumeric.layers_00_02_09_10

theorem cells_00_02_09_10 : QTableValid (![0, 2, 11, 21] : Fin 4 → ℕ) layers_00_02_09_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_09_10

theorem valid_00_02_09_10 :
    SparseRowValid (![0, 2, 11, 21] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_00_02_09_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 11, 21] : Fin 4 → ℕ) i) = 34 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 11 + 21 = 34
      decide
    have hzsq : (∑ i, (((![0, 2, 11, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 566 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 11^2 + 21^2 = 566
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_09_10
#print axioms Paper7MomentGapNumeric.valid_00_02_09_10

def qvalues_00_02_09_10 : Fin 19 → ℕ := ![0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_09_10

theorem row_00_02_09_10 : b4RowContribution (![0, 2, 11, 21] : Fin 4 → ℕ) = 6 := by
  calc
    b4RowContribution (![0, 2, 11, 21] : Fin 4 → ℕ) =
        sparseRowValue ({2} : Finset (Fin 19)) (fun _ => layers_00_02_09_10) :=
      sparseRow_sound (![0, 2, 11, 21] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_00_02_09_10) valid_00_02_09_10
    _ = 6 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_09_10 Q := by
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
        _ = 6 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_09_10

theorem weighted_00_02_09_10 : b4RawGapContribution ![0, 2, 9, 10] = 144 := by
  calc
    b4RawGapContribution ![0, 2, 9, 10] = b4GapPatternWeight 2 9 10 * 6 :=
      b4GapContribution_from_row 0 2 9 10 6 row_00_02_09_10
    _ = 144 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_09_10

theorem row_00_02_09_11 : b4RowContribution (![0, 2, 11, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 11, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 11 + 22 = 35
    decide
  have hzsq : (∑ i, (((![0, 2, 11, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 609 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 11^2 + 22^2 = 609
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_09_11

theorem weighted_00_02_09_11 : b4RawGapContribution ![0, 2, 9, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 9, 11] = b4GapPatternWeight 2 9 11 * 0 :=
      b4GapContribution_from_row 0 2 9 11 0 row_00_02_09_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_09_11

theorem row_00_02_09_12 : b4RowContribution (![0, 2, 11, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 11, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 11 + 23 = 36
    decide
  have hzsq : (∑ i, (((![0, 2, 11, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 654 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 11^2 + 23^2 = 654
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_09_12

theorem weighted_00_02_09_12 : b4RawGapContribution ![0, 2, 9, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 9, 12] = b4GapPatternWeight 2 9 12 * 0 :=
      b4GapContribution_from_row 0 2 9 12 0 row_00_02_09_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_09_12

theorem row_00_02_09_13 : b4RowContribution (![0, 2, 11, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 11, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 11 + 24 = 37
    decide
  have hzsq : (∑ i, (((![0, 2, 11, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 701 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 11^2 + 24^2 = 701
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_09_13

theorem weighted_00_02_09_13 : b4RawGapContribution ![0, 2, 9, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 9, 13] = b4GapPatternWeight 2 9 13 * 0 :=
      b4GapContribution_from_row 0 2 9 13 0 row_00_02_09_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_09_13

def dvalues_00_02_09 : Fin 14 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_02_09

theorem dblock_00_02_09 : b4GapPatternDBlock 0 2 9 = 144 := by
  calc
    b4GapPatternDBlock 0 2 9 = ∑ d : Fin 14, dvalues_00_02_09 d := by
      apply b4GapDBlock_of_rows 0 2 9 dvalues_00_02_09
      intro d
      fin_cases d
      · exact weighted_00_02_09_00
      · exact weighted_00_02_09_01
      · exact weighted_00_02_09_02
      · exact weighted_00_02_09_03
      · exact weighted_00_02_09_04
      · exact weighted_00_02_09_05
      · exact weighted_00_02_09_06
      · exact weighted_00_02_09_07
      · exact weighted_00_02_09_08
      · exact weighted_00_02_09_09
      · exact weighted_00_02_09_10
      · exact weighted_00_02_09_11
      · exact weighted_00_02_09_12
      · exact weighted_00_02_09_13
    _ = 144 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_02_09

end Paper7MomentGapNumeric
