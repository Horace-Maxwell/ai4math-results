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

theorem row_01_01_09_00 : b4RowContribution (![1, 2, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 11, 11] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 11 + 11 = 25
    decide
  have hzsq : (∑ i, (((![1, 2, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 247 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 11^2 + 11^2 = 247
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_09_00

theorem weighted_01_01_09_00 : b4RawGapContribution ![1, 1, 9, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 9, 0] = b4GapPatternWeight 1 9 0 * 0 :=
      b4GapContribution_from_row 1 1 9 0 0 row_01_01_09_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_09_00

theorem row_01_01_09_01 : b4RowContribution (![1, 2, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 11, 12] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 11 + 12 = 26
    decide
  have hzsq : (∑ i, (((![1, 2, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 11^2 + 12^2 = 270
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_09_01

theorem weighted_01_01_09_01 : b4RawGapContribution ![1, 1, 9, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 9, 1] = b4GapPatternWeight 1 9 1 * 0 :=
      b4GapContribution_from_row 1 1 9 1 0 row_01_01_09_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_09_01

theorem row_01_01_09_02 : b4RowContribution (![1, 2, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 11, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 11 + 13 = 27
    decide
  have hzsq : (∑ i, (((![1, 2, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 295 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 11^2 + 13^2 = 295
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_09_02

theorem weighted_01_01_09_02 : b4RawGapContribution ![1, 1, 9, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 9, 2] = b4GapPatternWeight 1 9 2 * 0 :=
      b4GapContribution_from_row 1 1 9 2 0 row_01_01_09_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_09_02

theorem row_01_01_09_03 : b4RowContribution (![1, 2, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 11, 14] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 11 + 14 = 28
    decide
  have hzsq : (∑ i, (((![1, 2, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 322 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 11^2 + 14^2 = 322
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_09_03

theorem weighted_01_01_09_03 : b4RawGapContribution ![1, 1, 9, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 9, 3] = b4GapPatternWeight 1 9 3 * 0 :=
      b4GapContribution_from_row 1 1 9 3 0 row_01_01_09_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_09_03

theorem row_01_01_09_04 : b4RowContribution (![1, 2, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 11, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 11 + 15 = 29
    decide
  have hzsq : (∑ i, (((![1, 2, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 351 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 11^2 + 15^2 = 351
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_09_04

theorem weighted_01_01_09_04 : b4RawGapContribution ![1, 1, 9, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 9, 4] = b4GapPatternWeight 1 9 4 * 0 :=
      b4GapContribution_from_row 1 1 9 4 0 row_01_01_09_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_09_04

theorem row_01_01_09_05 : b4RowContribution (![1, 2, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 11, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 11 + 16 = 30
    decide
  have hzsq : (∑ i, (((![1, 2, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 382 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 11^2 + 16^2 = 382
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_09_05

theorem weighted_01_01_09_05 : b4RawGapContribution ![1, 1, 9, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 9, 5] = b4GapPatternWeight 1 9 5 * 0 :=
      b4GapContribution_from_row 1 1 9 5 0 row_01_01_09_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_09_05

theorem row_01_01_09_06 : b4RowContribution (![1, 2, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 11, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 11 + 17 = 31
    decide
  have hzsq : (∑ i, (((![1, 2, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 415 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 11^2 + 17^2 = 415
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_09_06

theorem weighted_01_01_09_06 : b4RawGapContribution ![1, 1, 9, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 9, 6] = b4GapPatternWeight 1 9 6 * 0 :=
      b4GapContribution_from_row 1 1 9 6 0 row_01_01_09_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_09_06

theorem row_01_01_09_07 : b4RowContribution (![1, 2, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 11, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 11 + 18 = 32
    decide
  have hzsq : (∑ i, (((![1, 2, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 11^2 + 18^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_09_07

theorem weighted_01_01_09_07 : b4RawGapContribution ![1, 1, 9, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 9, 7] = b4GapPatternWeight 1 9 7 * 0 :=
      b4GapContribution_from_row 1 1 9 7 0 row_01_01_09_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_09_07

theorem row_01_01_09_08 : b4RowContribution (![1, 2, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 11, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 11 + 19 = 33
    decide
  have hzsq : (∑ i, (((![1, 2, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 487 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 11^2 + 19^2 = 487
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_09_08

theorem weighted_01_01_09_08 : b4RawGapContribution ![1, 1, 9, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 9, 8] = b4GapPatternWeight 1 9 8 * 0 :=
      b4GapContribution_from_row 1 1 9 8 0 row_01_01_09_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_09_08

theorem row_01_01_09_09 : b4RowContribution (![1, 2, 11, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 11, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 11 + 20 = 34
    decide
  have hzsq : (∑ i, (((![1, 2, 11, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 526 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 11^2 + 20^2 = 526
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_09_09

theorem weighted_01_01_09_09 : b4RawGapContribution ![1, 1, 9, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 9, 9] = b4GapPatternWeight 1 9 9 * 0 :=
      b4GapContribution_from_row 1 1 9 9 0 row_01_01_09_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_09_09

def layers_01_01_09_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 27, 33, 39, 45, 51, 57, 63, 68, 71, 72, 72, 72, 72, 72]]
#print axioms Paper7MomentGapNumeric.layers_01_01_09_10

theorem cells_01_01_09_10 : QTableValid (![1, 2, 11, 21] : Fin 4 → ℕ) layers_01_01_09_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_09_10

theorem valid_01_01_09_10 :
    SparseRowValid (![1, 2, 11, 21] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_01_01_09_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 11, 21] : Fin 4 → ℕ) i) = 35 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 11 + 21 = 35
      decide
    have hzsq : (∑ i, (((![1, 2, 11, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 567 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 11^2 + 21^2 = 567
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_09_10
#print axioms Paper7MomentGapNumeric.valid_01_01_09_10

def qvalues_01_01_09_10 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_09_10

theorem row_01_01_09_10 : b4RowContribution (![1, 2, 11, 21] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![1, 2, 11, 21] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_01_01_09_10) :=
      sparseRow_sound (![1, 2, 11, 21] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_01_01_09_10) valid_01_01_09_10
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_09_10 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 1 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_09_10

theorem weighted_01_01_09_10 : b4RawGapContribution ![1, 1, 9, 10] = 24 := by
  calc
    b4RawGapContribution ![1, 1, 9, 10] = b4GapPatternWeight 1 9 10 * 1 :=
      b4GapContribution_from_row 1 1 9 10 1 row_01_01_09_10
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_09_10

theorem row_01_01_09_11 : b4RowContribution (![1, 2, 11, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 11, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 11 + 22 = 36
    decide
  have hzsq : (∑ i, (((![1, 2, 11, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 610 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 11^2 + 22^2 = 610
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_09_11

theorem weighted_01_01_09_11 : b4RawGapContribution ![1, 1, 9, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 9, 11] = b4GapPatternWeight 1 9 11 * 0 :=
      b4GapContribution_from_row 1 1 9 11 0 row_01_01_09_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_09_11

theorem row_01_01_09_12 : b4RowContribution (![1, 2, 11, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 11, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 11 + 23 = 37
    decide
  have hzsq : (∑ i, (((![1, 2, 11, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 655 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 11^2 + 23^2 = 655
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_09_12

theorem weighted_01_01_09_12 : b4RawGapContribution ![1, 1, 9, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 9, 12] = b4GapPatternWeight 1 9 12 * 0 :=
      b4GapContribution_from_row 1 1 9 12 0 row_01_01_09_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_09_12

def dvalues_01_01_09 : Fin 13 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_01_09

theorem dblock_01_01_09 : b4GapPatternDBlock 1 1 9 = 24 := by
  calc
    b4GapPatternDBlock 1 1 9 = ∑ d : Fin 13, dvalues_01_01_09 d := by
      apply b4GapDBlock_of_rows 1 1 9 dvalues_01_01_09
      intro d
      fin_cases d
      · exact weighted_01_01_09_00
      · exact weighted_01_01_09_01
      · exact weighted_01_01_09_02
      · exact weighted_01_01_09_03
      · exact weighted_01_01_09_04
      · exact weighted_01_01_09_05
      · exact weighted_01_01_09_06
      · exact weighted_01_01_09_07
      · exact weighted_01_01_09_08
      · exact weighted_01_01_09_09
      · exact weighted_01_01_09_10
      · exact weighted_01_01_09_11
      · exact weighted_01_01_09_12
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_01_09

end Paper7MomentGapNumeric
