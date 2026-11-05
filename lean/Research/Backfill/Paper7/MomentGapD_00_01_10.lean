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

def layers_00_01_10_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 23, 21, 19, 17, 15, 13, 11]]
#print axioms Paper7MomentGapNumeric.layers_00_01_10_00

theorem cells_00_01_10_00 : QTableValid (![0, 1, 11, 11] : Fin 4 → ℕ) layers_00_01_10_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_10_00

theorem valid_00_01_10_00 :
    SparseRowValid (![0, 1, 11, 11] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_00_01_10_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 11, 11] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 11 + 11 = 23
      decide
    have hzsq : (∑ i, (((![0, 1, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 243 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 11^2 + 11^2 = 243
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_10_00
#print axioms Paper7MomentGapNumeric.valid_00_01_10_00

def qvalues_00_01_10_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_10_00

theorem row_00_01_10_00 : b4RowContribution (![0, 1, 11, 11] : Fin 4 → ℕ) = 13 := by
  calc
    b4RowContribution (![0, 1, 11, 11] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_00_01_10_00) :=
      sparseRow_sound (![0, 1, 11, 11] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_00_01_10_00) valid_00_01_10_00
    _ = 13 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_10_00 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 13 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_10_00

theorem weighted_00_01_10_00 : b4RawGapContribution ![0, 1, 10, 0] = 156 := by
  calc
    b4RawGapContribution ![0, 1, 10, 0] = b4GapPatternWeight 1 10 0 * 13 :=
      b4GapContribution_from_row 0 1 10 0 13 row_00_01_10_00
    _ = 156 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_00

theorem row_00_01_10_01 : b4RowContribution (![0, 1, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 11, 12] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 11 + 12 = 24
    decide
  have hzsq : (∑ i, (((![0, 1, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 266 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 11^2 + 12^2 = 266
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_10_01

theorem weighted_00_01_10_01 : b4RawGapContribution ![0, 1, 10, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 10, 1] = b4GapPatternWeight 1 10 1 * 0 :=
      b4GapContribution_from_row 0 1 10 1 0 row_00_01_10_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_01

def layers_00_01_10_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 24, 24, 23, 21, 19, 17, 15]]
#print axioms Paper7MomentGapNumeric.layers_00_01_10_02

theorem cells_00_01_10_02 : QTableValid (![0, 1, 11, 13] : Fin 4 → ℕ) layers_00_01_10_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_10_02

theorem valid_00_01_10_02 :
    SparseRowValid (![0, 1, 11, 13] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_01_10_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 11, 13] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 11 + 13 = 25
      decide
    have hzsq : (∑ i, (((![0, 1, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 291 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 11^2 + 13^2 = 291
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_10_02
#print axioms Paper7MomentGapNumeric.valid_00_01_10_02

def qvalues_00_01_10_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_10_02

theorem row_00_01_10_02 : b4RowContribution (![0, 1, 11, 13] : Fin 4 → ℕ) = 19 := by
  calc
    b4RowContribution (![0, 1, 11, 13] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_00_01_10_02) :=
      sparseRow_sound (![0, 1, 11, 13] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_01_10_02) valid_00_01_10_02
    _ = 19 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_10_02 Q := by
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
        _ = 19 := by decide
#print axioms Paper7MomentGapNumeric.row_00_01_10_02

theorem weighted_00_01_10_02 : b4RawGapContribution ![0, 1, 10, 2] = 456 := by
  calc
    b4RawGapContribution ![0, 1, 10, 2] = b4GapPatternWeight 1 10 2 * 19 :=
      b4GapContribution_from_row 0 1 10 2 19 row_00_01_10_02
    _ = 456 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_02

theorem row_00_01_10_03 : b4RowContribution (![0, 1, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 11, 14] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 11 + 14 = 26
    decide
  have hzsq : (∑ i, (((![0, 1, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 318 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 11^2 + 14^2 = 318
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_10_03

theorem weighted_00_01_10_03 : b4RawGapContribution ![0, 1, 10, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 10, 3] = b4GapPatternWeight 1 10 3 * 0 :=
      b4GapContribution_from_row 0 1 10 3 0 row_00_01_10_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_03

theorem row_00_01_10_04 : b4RowContribution (![0, 1, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 11, 15] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 11 + 15 = 27
    decide
  have hzsq : (∑ i, (((![0, 1, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 347 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 11^2 + 15^2 = 347
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_10_04

theorem weighted_00_01_10_04 : b4RawGapContribution ![0, 1, 10, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 10, 4] = b4GapPatternWeight 1 10 4 * 0 :=
      b4GapContribution_from_row 0 1 10 4 0 row_00_01_10_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_04

theorem row_00_01_10_05 : b4RowContribution (![0, 1, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 11, 16] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 11 + 16 = 28
    decide
  have hzsq : (∑ i, (((![0, 1, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 378 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 11^2 + 16^2 = 378
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_10_05

theorem weighted_00_01_10_05 : b4RawGapContribution ![0, 1, 10, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 10, 5] = b4GapPatternWeight 1 10 5 * 0 :=
      b4GapContribution_from_row 0 1 10 5 0 row_00_01_10_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_05

theorem row_00_01_10_06 : b4RowContribution (![0, 1, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 11, 17] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 11 + 17 = 29
    decide
  have hzsq : (∑ i, (((![0, 1, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 411 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 11^2 + 17^2 = 411
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_10_06

theorem weighted_00_01_10_06 : b4RawGapContribution ![0, 1, 10, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 10, 6] = b4GapPatternWeight 1 10 6 * 0 :=
      b4GapContribution_from_row 0 1 10 6 0 row_00_01_10_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_06

theorem row_00_01_10_07 : b4RowContribution (![0, 1, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 11, 18] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 11 + 18 = 30
    decide
  have hzsq : (∑ i, (((![0, 1, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 446 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 11^2 + 18^2 = 446
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_10_07

theorem weighted_00_01_10_07 : b4RawGapContribution ![0, 1, 10, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 10, 7] = b4GapPatternWeight 1 10 7 * 0 :=
      b4GapContribution_from_row 0 1 10 7 0 row_00_01_10_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_07

theorem row_00_01_10_08 : b4RowContribution (![0, 1, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 11, 19] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 11 + 19 = 31
    decide
  have hzsq : (∑ i, (((![0, 1, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 483 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 11^2 + 19^2 = 483
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_10_08

theorem weighted_00_01_10_08 : b4RawGapContribution ![0, 1, 10, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 10, 8] = b4GapPatternWeight 1 10 8 * 0 :=
      b4GapContribution_from_row 0 1 10 8 0 row_00_01_10_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_08

theorem row_00_01_10_09 : b4RowContribution (![0, 1, 11, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 11, 20] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 11 + 20 = 32
    decide
  have hzsq : (∑ i, (((![0, 1, 11, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 522 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 11^2 + 20^2 = 522
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_10_09

theorem weighted_00_01_10_09 : b4RawGapContribution ![0, 1, 10, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 10, 9] = b4GapPatternWeight 1 10 9 * 0 :=
      b4GapContribution_from_row 0 1 10 9 0 row_00_01_10_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_09

theorem row_00_01_10_10 : b4RowContribution (![0, 1, 11, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 11, 21] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 11 + 21 = 33
    decide
  have hzsq : (∑ i, (((![0, 1, 11, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 563 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 11^2 + 21^2 = 563
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_10_10

theorem weighted_00_01_10_10 : b4RawGapContribution ![0, 1, 10, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 10, 10] = b4GapPatternWeight 1 10 10 * 0 :=
      b4GapContribution_from_row 0 1 10 10 0 row_00_01_10_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_10

theorem row_00_01_10_11 : b4RowContribution (![0, 1, 11, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 11, 22] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 11 + 22 = 34
    decide
  have hzsq : (∑ i, (((![0, 1, 11, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 606 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 11^2 + 22^2 = 606
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_10_11

theorem weighted_00_01_10_11 : b4RawGapContribution ![0, 1, 10, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 10, 11] = b4GapPatternWeight 1 10 11 * 0 :=
      b4GapContribution_from_row 0 1 10 11 0 row_00_01_10_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_11

theorem row_00_01_10_12 : b4RowContribution (![0, 1, 11, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 11, 23] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 11 + 23 = 35
    decide
  have hzsq : (∑ i, (((![0, 1, 11, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 651 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 11^2 + 23^2 = 651
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_10_12

theorem weighted_00_01_10_12 : b4RawGapContribution ![0, 1, 10, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 10, 12] = b4GapPatternWeight 1 10 12 * 0 :=
      b4GapContribution_from_row 0 1 10 12 0 row_00_01_10_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_12

theorem row_00_01_10_13 : b4RowContribution (![0, 1, 11, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 11, 24] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 11 + 24 = 36
    decide
  have hzsq : (∑ i, (((![0, 1, 11, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 698 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 11^2 + 24^2 = 698
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_10_13

theorem weighted_00_01_10_13 : b4RawGapContribution ![0, 1, 10, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 10, 13] = b4GapPatternWeight 1 10 13 * 0 :=
      b4GapContribution_from_row 0 1 10 13 0 row_00_01_10_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_13

theorem row_00_01_10_14 : b4RowContribution (![0, 1, 11, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 11, 25] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 11 + 25 = 37
    decide
  have hzsq : (∑ i, (((![0, 1, 11, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 747 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 11^2 + 25^2 = 747
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_10_14

theorem weighted_00_01_10_14 : b4RawGapContribution ![0, 1, 10, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 10, 14] = b4GapPatternWeight 1 10 14 * 0 :=
      b4GapContribution_from_row 0 1 10 14 0 row_00_01_10_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_10_14

def dvalues_00_01_10 : Fin 15 → ℕ := ![156, 0, 456, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_01_10

theorem dblock_00_01_10 : b4GapPatternDBlock 0 1 10 = 612 := by
  calc
    b4GapPatternDBlock 0 1 10 = ∑ d : Fin 15, dvalues_00_01_10 d := by
      apply b4GapDBlock_of_rows 0 1 10 dvalues_00_01_10
      intro d
      fin_cases d
      · exact weighted_00_01_10_00
      · exact weighted_00_01_10_01
      · exact weighted_00_01_10_02
      · exact weighted_00_01_10_03
      · exact weighted_00_01_10_04
      · exact weighted_00_01_10_05
      · exact weighted_00_01_10_06
      · exact weighted_00_01_10_07
      · exact weighted_00_01_10_08
      · exact weighted_00_01_10_09
      · exact weighted_00_01_10_10
      · exact weighted_00_01_10_11
      · exact weighted_00_01_10_12
      · exact weighted_00_01_10_13
      · exact weighted_00_01_10_14
    _ = 612 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_01_10

end Paper7MomentGapNumeric
