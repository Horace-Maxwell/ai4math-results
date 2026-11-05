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

def layers_01_04_05_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 12, 12, 12, 12, 12, 11, 9, 7, 5, 3, 1, 0, 0], ![1, 4, 9, 16, 25, 36, 48, 60, 72, 84, 96, 106, 112, 114, 112, 106, 96, 84, 72]]
#print axioms Paper7MomentGapNumeric.layers_01_04_05_00

theorem cells_01_04_05_00 : QTableValid (![1, 5, 10, 10] : Fin 4 → ℕ) layers_01_04_05_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_04_05_00

theorem valid_01_04_05_00 :
    SparseRowValid (![1, 5, 10, 10] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_04_05_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 5, 10, 10] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 1 + 5 + 10 + 10 = 26
      decide
    have hzsq : (∑ i, (((![1, 5, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 226 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 5^2 + 10^2 + 10^2 = 226
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_04_05_00
#print axioms Paper7MomentGapNumeric.valid_01_04_05_00

def qvalues_01_04_05_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_04_05_00

theorem row_01_04_05_00 : b4RowContribution (![1, 5, 10, 10] : Fin 4 → ℕ) = 96 := by
  calc
    b4RowContribution (![1, 5, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_04_05_00) :=
      sparseRow_sound (![1, 5, 10, 10] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_04_05_00) valid_01_04_05_00
    _ = 96 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_04_05_00 Q := by
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
        _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.row_01_04_05_00

theorem weighted_01_04_05_00 : b4RawGapContribution ![1, 4, 5, 0] = 1152 := by
  calc
    b4RawGapContribution ![1, 4, 5, 0] = b4GapPatternWeight 4 5 0 * 96 :=
      b4GapContribution_from_row 1 4 5 0 96 row_01_04_05_00
    _ = 1152 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_05_00

theorem row_01_04_05_01 : b4RowContribution (![1, 5, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 10, 11] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 10 + 11 = 27
    decide
  have hzsq : (∑ i, (((![1, 5, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 247 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 10^2 + 11^2 = 247
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_05_01

theorem weighted_01_04_05_01 : b4RawGapContribution ![1, 4, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 5, 1] = b4GapPatternWeight 4 5 1 * 0 :=
      b4GapContribution_from_row 1 4 5 1 0 row_01_04_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_05_01

def layers_01_04_05_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 12, 12, 12, 12, 12, 11, 9, 7, 5, 3, 1, 0, 0], ![1, 4, 9, 16, 25, 36, 48, 60, 72, 84, 96, 107, 116, 122, 124, 122, 116, 107, 96]]
#print axioms Paper7MomentGapNumeric.layers_01_04_05_02

theorem cells_01_04_05_02 : QTableValid (![1, 5, 10, 12] : Fin 4 → ℕ) layers_01_04_05_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_04_05_02

theorem valid_01_04_05_02 :
    SparseRowValid (![1, 5, 10, 12] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_04_05_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 5, 10, 12] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 1 + 5 + 10 + 12 = 28
      decide
    have hzsq : (∑ i, (((![1, 5, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 5^2 + 10^2 + 12^2 = 270
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_04_05_02
#print axioms Paper7MomentGapNumeric.valid_01_04_05_02

def qvalues_01_04_05_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_04_05_02

theorem row_01_04_05_02 : b4RowContribution (![1, 5, 10, 12] : Fin 4 → ℕ) = 84 := by
  calc
    b4RowContribution (![1, 5, 10, 12] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_04_05_02) :=
      sparseRow_sound (![1, 5, 10, 12] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_04_05_02) valid_01_04_05_02
    _ = 84 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_04_05_02 Q := by
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
        _ = 84 := by decide
#print axioms Paper7MomentGapNumeric.row_01_04_05_02

theorem weighted_01_04_05_02 : b4RawGapContribution ![1, 4, 5, 2] = 2016 := by
  calc
    b4RawGapContribution ![1, 4, 5, 2] = b4GapPatternWeight 4 5 2 * 84 :=
      b4GapContribution_from_row 1 4 5 2 84 row_01_04_05_02
    _ = 2016 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_05_02

theorem row_01_04_05_03 : b4RowContribution (![1, 5, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 10, 13] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 10 + 13 = 29
    decide
  have hzsq : (∑ i, (((![1, 5, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 295 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 10^2 + 13^2 = 295
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_05_03

theorem weighted_01_04_05_03 : b4RawGapContribution ![1, 4, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 5, 3] = b4GapPatternWeight 4 5 3 * 0 :=
      b4GapContribution_from_row 1 4 5 3 0 row_01_04_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_05_03

theorem row_01_04_05_04 : b4RowContribution (![1, 5, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 10, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 10 + 14 = 30
    decide
  have hzsq : (∑ i, (((![1, 5, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 322 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 10^2 + 14^2 = 322
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_05_04

theorem weighted_01_04_05_04 : b4RawGapContribution ![1, 4, 5, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 5, 4] = b4GapPatternWeight 4 5 4 * 0 :=
      b4GapContribution_from_row 1 4 5 4 0 row_01_04_05_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_05_04

theorem row_01_04_05_05 : b4RowContribution (![1, 5, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 10, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 10 + 15 = 31
    decide
  have hzsq : (∑ i, (((![1, 5, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 351 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 10^2 + 15^2 = 351
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_05_05

theorem weighted_01_04_05_05 : b4RawGapContribution ![1, 4, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 5, 5] = b4GapPatternWeight 4 5 5 * 0 :=
      b4GapContribution_from_row 1 4 5 5 0 row_01_04_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_05_05

theorem row_01_04_05_06 : b4RowContribution (![1, 5, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 10, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 10 + 16 = 32
    decide
  have hzsq : (∑ i, (((![1, 5, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 382 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 10^2 + 16^2 = 382
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_05_06

theorem weighted_01_04_05_06 : b4RawGapContribution ![1, 4, 5, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 5, 6] = b4GapPatternWeight 4 5 6 * 0 :=
      b4GapContribution_from_row 1 4 5 6 0 row_01_04_05_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_05_06

theorem row_01_04_05_07 : b4RowContribution (![1, 5, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 10, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 10 + 17 = 33
    decide
  have hzsq : (∑ i, (((![1, 5, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 415 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 10^2 + 17^2 = 415
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_05_07

theorem weighted_01_04_05_07 : b4RawGapContribution ![1, 4, 5, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 5, 7] = b4GapPatternWeight 4 5 7 * 0 :=
      b4GapContribution_from_row 1 4 5 7 0 row_01_04_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_05_07

theorem row_01_04_05_08 : b4RowContribution (![1, 5, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 10, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 10 + 18 = 34
    decide
  have hzsq : (∑ i, (((![1, 5, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 10^2 + 18^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_05_08

theorem weighted_01_04_05_08 : b4RawGapContribution ![1, 4, 5, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 5, 8] = b4GapPatternWeight 4 5 8 * 0 :=
      b4GapContribution_from_row 1 4 5 8 0 row_01_04_05_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_05_08

theorem row_01_04_05_09 : b4RowContribution (![1, 5, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 10, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 10 + 19 = 35
    decide
  have hzsq : (∑ i, (((![1, 5, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 487 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 10^2 + 19^2 = 487
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_05_09

theorem weighted_01_04_05_09 : b4RawGapContribution ![1, 4, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 5, 9] = b4GapPatternWeight 4 5 9 * 0 :=
      b4GapContribution_from_row 1 4 5 9 0 row_01_04_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_05_09

theorem row_01_04_05_10 : b4RowContribution (![1, 5, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 10, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 10 + 20 = 36
    decide
  have hzsq : (∑ i, (((![1, 5, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 526 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 10^2 + 20^2 = 526
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_05_10

theorem weighted_01_04_05_10 : b4RawGapContribution ![1, 4, 5, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 5, 10] = b4GapPatternWeight 4 5 10 * 0 :=
      b4GapContribution_from_row 1 4 5 10 0 row_01_04_05_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_05_10

theorem row_01_04_05_11 : b4RowContribution (![1, 5, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 10, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 10 + 21 = 37
    decide
  have hzsq : (∑ i, (((![1, 5, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 567 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 10^2 + 21^2 = 567
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_05_11

theorem weighted_01_04_05_11 : b4RawGapContribution ![1, 4, 5, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 5, 11] = b4GapPatternWeight 4 5 11 * 0 :=
      b4GapContribution_from_row 1 4 5 11 0 row_01_04_05_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_05_11

def dvalues_01_04_05 : Fin 12 → ℕ := ![1152, 0, 2016, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_04_05

theorem dblock_01_04_05 : b4GapPatternDBlock 1 4 5 = 3168 := by
  calc
    b4GapPatternDBlock 1 4 5 = ∑ d : Fin 12, dvalues_01_04_05 d := by
      apply b4GapDBlock_of_rows 1 4 5 dvalues_01_04_05
      intro d
      fin_cases d
      · exact weighted_01_04_05_00
      · exact weighted_01_04_05_01
      · exact weighted_01_04_05_02
      · exact weighted_01_04_05_03
      · exact weighted_01_04_05_04
      · exact weighted_01_04_05_05
      · exact weighted_01_04_05_06
      · exact weighted_01_04_05_07
      · exact weighted_01_04_05_08
      · exact weighted_01_04_05_09
      · exact weighted_01_04_05_10
      · exact weighted_01_04_05_11
    _ = 3168 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_04_05

end Paper7MomentGapNumeric
