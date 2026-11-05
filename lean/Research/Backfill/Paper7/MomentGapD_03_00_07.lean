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

theorem row_03_00_07_00 : b4RowContribution (![3, 3, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 10, 10] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 10 + 10 = 26
    decide
  have hzsq : (∑ i, (((![3, 3, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 218 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 10^2 + 10^2 = 218
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_07_00

theorem weighted_03_00_07_00 : b4RawGapContribution ![3, 0, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 7, 0] = b4GapPatternWeight 0 7 0 * 0 :=
      b4GapContribution_from_row 3 0 7 0 0 row_03_00_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_07_00

def layers_03_00_07_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 15, 16, 16, 16, 16, 16, 15, 13, 10, 6, 3, 1, 0, 0], ![1, 4, 10, 20, 33, 48, 64, 80, 96, 112, 128, 143, 155, 162, 162, 155, 143, 128, 112]]
#print axioms Paper7MomentGapNumeric.layers_03_00_07_01

theorem cells_03_00_07_01 : QTableValid (![3, 3, 10, 11] : Fin 4 → ℕ) layers_03_00_07_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_00_07_01

theorem valid_03_00_07_01 :
    SparseRowValid (![3, 3, 10, 11] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_03_00_07_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 3, 10, 11] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 3 + 3 + 10 + 11 = 27
      decide
    have hzsq : (∑ i, (((![3, 3, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 239 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 3^2 + 10^2 + 11^2 = 239
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_00_07_01
#print axioms Paper7MomentGapNumeric.valid_03_00_07_01

def qvalues_03_00_07_01 : Fin 19 → ℕ := ![0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_00_07_01

theorem row_03_00_07_01 : b4RowContribution (![3, 3, 10, 11] : Fin 4 → ℕ) = 10 := by
  calc
    b4RowContribution (![3, 3, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({2} : Finset (Fin 19)) (fun _ => layers_03_00_07_01) :=
      sparseRow_sound (![3, 3, 10, 11] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_03_00_07_01) valid_03_00_07_01
    _ = 10 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_00_07_01 Q := by
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
        _ = 10 := by decide
#print axioms Paper7MomentGapNumeric.row_03_00_07_01

theorem weighted_03_00_07_01 : b4RawGapContribution ![3, 0, 7, 1] = 120 := by
  calc
    b4RawGapContribution ![3, 0, 7, 1] = b4GapPatternWeight 0 7 1 * 10 :=
      b4GapContribution_from_row 3 0 7 1 10 row_03_00_07_01
    _ = 120 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_07_01

theorem row_03_00_07_02 : b4RowContribution (![3, 3, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 10, 12] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 10 + 12 = 28
    decide
  have hzsq : (∑ i, (((![3, 3, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 262 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 10^2 + 12^2 = 262
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_07_02

theorem weighted_03_00_07_02 : b4RawGapContribution ![3, 0, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 7, 2] = b4GapPatternWeight 0 7 2 * 0 :=
      b4GapContribution_from_row 3 0 7 2 0 row_03_00_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_07_02

def layers_03_00_07_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 15, 16, 16, 16, 16, 16, 15, 13, 10, 6, 3, 1, 0, 0], ![1, 4, 10, 20, 33, 48, 64, 80, 96, 112, 128, 143, 156, 166, 171, 171, 166, 156, 143]]
#print axioms Paper7MomentGapNumeric.layers_03_00_07_03

theorem cells_03_00_07_03 : QTableValid (![3, 3, 10, 13] : Fin 4 → ℕ) layers_03_00_07_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_00_07_03

theorem valid_03_00_07_03 :
    SparseRowValid (![3, 3, 10, 13] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_00_07_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 3, 10, 13] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 3 + 3 + 10 + 13 = 29
      decide
    have hzsq : (∑ i, (((![3, 3, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 287 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 3^2 + 10^2 + 13^2 = 287
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_00_07_03
#print axioms Paper7MomentGapNumeric.valid_03_00_07_03

def qvalues_03_00_07_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_00_07_03

theorem row_03_00_07_03 : b4RowContribution (![3, 3, 10, 13] : Fin 4 → ℕ) = 48 := by
  calc
    b4RowContribution (![3, 3, 10, 13] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_03_00_07_03) :=
      sparseRow_sound (![3, 3, 10, 13] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_00_07_03) valid_03_00_07_03
    _ = 48 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_00_07_03 Q := by
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
        _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.row_03_00_07_03

theorem weighted_03_00_07_03 : b4RawGapContribution ![3, 0, 7, 3] = 576 := by
  calc
    b4RawGapContribution ![3, 0, 7, 3] = b4GapPatternWeight 0 7 3 * 48 :=
      b4GapContribution_from_row 3 0 7 3 48 row_03_00_07_03
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_07_03

theorem row_03_00_07_04 : b4RowContribution (![3, 3, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 10, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 10 + 14 = 30
    decide
  have hzsq : (∑ i, (((![3, 3, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 314 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 10^2 + 14^2 = 314
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_07_04

theorem weighted_03_00_07_04 : b4RawGapContribution ![3, 0, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 7, 4] = b4GapPatternWeight 0 7 4 * 0 :=
      b4GapContribution_from_row 3 0 7 4 0 row_03_00_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_07_04

theorem row_03_00_07_05 : b4RowContribution (![3, 3, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 10, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 10 + 15 = 31
    decide
  have hzsq : (∑ i, (((![3, 3, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 343 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 10^2 + 15^2 = 343
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_07_05

theorem weighted_03_00_07_05 : b4RawGapContribution ![3, 0, 7, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 7, 5] = b4GapPatternWeight 0 7 5 * 0 :=
      b4GapContribution_from_row 3 0 7 5 0 row_03_00_07_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_07_05

theorem row_03_00_07_06 : b4RowContribution (![3, 3, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 10, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 10 + 16 = 32
    decide
  have hzsq : (∑ i, (((![3, 3, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 374 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 10^2 + 16^2 = 374
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_07_06

theorem weighted_03_00_07_06 : b4RawGapContribution ![3, 0, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 7, 6] = b4GapPatternWeight 0 7 6 * 0 :=
      b4GapContribution_from_row 3 0 7 6 0 row_03_00_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_07_06

theorem row_03_00_07_07 : b4RowContribution (![3, 3, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 10, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 10 + 17 = 33
    decide
  have hzsq : (∑ i, (((![3, 3, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 407 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 10^2 + 17^2 = 407
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_07_07

theorem weighted_03_00_07_07 : b4RawGapContribution ![3, 0, 7, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 7, 7] = b4GapPatternWeight 0 7 7 * 0 :=
      b4GapContribution_from_row 3 0 7 7 0 row_03_00_07_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_07_07

theorem row_03_00_07_08 : b4RowContribution (![3, 3, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 10, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 10 + 18 = 34
    decide
  have hzsq : (∑ i, (((![3, 3, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 442 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 10^2 + 18^2 = 442
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_07_08

theorem weighted_03_00_07_08 : b4RawGapContribution ![3, 0, 7, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 7, 8] = b4GapPatternWeight 0 7 8 * 0 :=
      b4GapContribution_from_row 3 0 7 8 0 row_03_00_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_07_08

theorem row_03_00_07_09 : b4RowContribution (![3, 3, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 10, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 10 + 19 = 35
    decide
  have hzsq : (∑ i, (((![3, 3, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 479 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 10^2 + 19^2 = 479
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_07_09

theorem weighted_03_00_07_09 : b4RawGapContribution ![3, 0, 7, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 7, 9] = b4GapPatternWeight 0 7 9 * 0 :=
      b4GapContribution_from_row 3 0 7 9 0 row_03_00_07_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_07_09

theorem row_03_00_07_10 : b4RowContribution (![3, 3, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 10, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 10 + 20 = 36
    decide
  have hzsq : (∑ i, (((![3, 3, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 518 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 10^2 + 20^2 = 518
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_07_10

theorem weighted_03_00_07_10 : b4RawGapContribution ![3, 0, 7, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 7, 10] = b4GapPatternWeight 0 7 10 * 0 :=
      b4GapContribution_from_row 3 0 7 10 0 row_03_00_07_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_07_10

theorem row_03_00_07_11 : b4RowContribution (![3, 3, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 10, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 10 + 21 = 37
    decide
  have hzsq : (∑ i, (((![3, 3, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 559 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 10^2 + 21^2 = 559
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_07_11

theorem weighted_03_00_07_11 : b4RawGapContribution ![3, 0, 7, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 7, 11] = b4GapPatternWeight 0 7 11 * 0 :=
      b4GapContribution_from_row 3 0 7 11 0 row_03_00_07_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_07_11

def dvalues_03_00_07 : Fin 12 → ℕ := ![0, 120, 0, 576, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_00_07

theorem dblock_03_00_07 : b4GapPatternDBlock 3 0 7 = 696 := by
  calc
    b4GapPatternDBlock 3 0 7 = ∑ d : Fin 12, dvalues_03_00_07 d := by
      apply b4GapDBlock_of_rows 3 0 7 dvalues_03_00_07
      intro d
      fin_cases d
      · exact weighted_03_00_07_00
      · exact weighted_03_00_07_01
      · exact weighted_03_00_07_02
      · exact weighted_03_00_07_03
      · exact weighted_03_00_07_04
      · exact weighted_03_00_07_05
      · exact weighted_03_00_07_06
      · exact weighted_03_00_07_07
      · exact weighted_03_00_07_08
      · exact weighted_03_00_07_09
      · exact weighted_03_00_07_10
      · exact weighted_03_00_07_11
    _ = 696 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_00_07

end Paper7MomentGapNumeric
