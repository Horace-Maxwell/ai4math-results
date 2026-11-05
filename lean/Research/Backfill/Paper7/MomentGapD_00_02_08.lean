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

theorem row_00_02_08_00 : b4RowContribution (![0, 2, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 10, 10] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 10 + 10 = 22
    decide
  have hzsq : (∑ i, (((![0, 2, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 204 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 10^2 + 10^2 = 204
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_08_00

theorem weighted_00_02_08_00 : b4RawGapContribution ![0, 2, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 8, 0] = b4GapPatternWeight 2 8 0 * 0 :=
      b4GapContribution_from_row 0 2 8 0 0 row_00_02_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_00

def layers_00_02_08_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 32, 32, 30, 27, 24, 21, 18, 15]]
#print axioms Paper7MomentGapNumeric.layers_00_02_08_01

theorem cells_00_02_08_01 : QTableValid (![0, 2, 10, 11] : Fin 4 → ℕ) layers_00_02_08_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_08_01

theorem valid_00_02_08_01 :
    SparseRowValid (![0, 2, 10, 11] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_02_08_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 10, 11] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 10 + 11 = 23
      decide
    have hzsq : (∑ i, (((![0, 2, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 225 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 10^2 + 11^2 = 225
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_08_01
#print axioms Paper7MomentGapNumeric.valid_00_02_08_01

def qvalues_00_02_08_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_08_01

theorem row_00_02_08_01 : b4RowContribution (![0, 2, 10, 11] : Fin 4 → ℕ) = 27 := by
  calc
    b4RowContribution (![0, 2, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_00_02_08_01) :=
      sparseRow_sound (![0, 2, 10, 11] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_02_08_01) valid_00_02_08_01
    _ = 27 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_08_01 Q := by
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
        _ = 27 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_08_01

theorem weighted_00_02_08_01 : b4RawGapContribution ![0, 2, 8, 1] = 648 := by
  calc
    b4RawGapContribution ![0, 2, 8, 1] = b4GapPatternWeight 2 8 1 * 27 :=
      b4GapContribution_from_row 0 2 8 1 27 row_00_02_08_01
    _ = 648 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_01

theorem row_00_02_08_02 : b4RowContribution (![0, 2, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 10, 12] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 10 + 12 = 24
    decide
  have hzsq : (∑ i, (((![0, 2, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 248 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 10^2 + 12^2 = 248
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_08_02

theorem weighted_00_02_08_02 : b4RawGapContribution ![0, 2, 8, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 8, 2] = b4GapPatternWeight 2 8 2 * 0 :=
      b4GapContribution_from_row 0 2 8 2 0 row_00_02_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_02

def layers_00_02_08_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 32, 33, 33, 32, 30, 27, 24, 21]]
#print axioms Paper7MomentGapNumeric.layers_00_02_08_03

theorem cells_00_02_08_03 : QTableValid (![0, 2, 10, 13] : Fin 4 → ℕ) layers_00_02_08_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_08_03

theorem valid_00_02_08_03 :
    SparseRowValid (![0, 2, 10, 13] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_02_08_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 10, 13] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 10 + 13 = 25
      decide
    have hzsq : (∑ i, (((![0, 2, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 273 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 10^2 + 13^2 = 273
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_08_03
#print axioms Paper7MomentGapNumeric.valid_00_02_08_03

def qvalues_00_02_08_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_08_03

theorem row_00_02_08_03 : b4RowContribution (![0, 2, 10, 13] : Fin 4 → ℕ) = 33 := by
  calc
    b4RowContribution (![0, 2, 10, 13] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_00_02_08_03) :=
      sparseRow_sound (![0, 2, 10, 13] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_02_08_03) valid_00_02_08_03
    _ = 33 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_08_03 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 33 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_08_03

theorem weighted_00_02_08_03 : b4RawGapContribution ![0, 2, 8, 3] = 792 := by
  calc
    b4RawGapContribution ![0, 2, 8, 3] = b4GapPatternWeight 2 8 3 * 33 :=
      b4GapContribution_from_row 0 2 8 3 33 row_00_02_08_03
    _ = 792 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_03

theorem row_00_02_08_04 : b4RowContribution (![0, 2, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 10, 14] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 10 + 14 = 26
    decide
  have hzsq : (∑ i, (((![0, 2, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 300 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 10^2 + 14^2 = 300
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_08_04

theorem weighted_00_02_08_04 : b4RawGapContribution ![0, 2, 8, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 8, 4] = b4GapPatternWeight 2 8 4 * 0 :=
      b4GapContribution_from_row 0 2 8 4 0 row_00_02_08_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_04

theorem row_00_02_08_05 : b4RowContribution (![0, 2, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 10, 15] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 10 + 15 = 27
    decide
  have hzsq : (∑ i, (((![0, 2, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 329 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 10^2 + 15^2 = 329
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_08_05

theorem weighted_00_02_08_05 : b4RawGapContribution ![0, 2, 8, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 8, 5] = b4GapPatternWeight 2 8 5 * 0 :=
      b4GapContribution_from_row 0 2 8 5 0 row_00_02_08_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_05

theorem row_00_02_08_06 : b4RowContribution (![0, 2, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 10, 16] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 10 + 16 = 28
    decide
  have hzsq : (∑ i, (((![0, 2, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 360 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 10^2 + 16^2 = 360
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_08_06

theorem weighted_00_02_08_06 : b4RawGapContribution ![0, 2, 8, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 8, 6] = b4GapPatternWeight 2 8 6 * 0 :=
      b4GapContribution_from_row 0 2 8 6 0 row_00_02_08_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_06

theorem row_00_02_08_07 : b4RowContribution (![0, 2, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 10, 17] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 10 + 17 = 29
    decide
  have hzsq : (∑ i, (((![0, 2, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 393 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 10^2 + 17^2 = 393
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_08_07

theorem weighted_00_02_08_07 : b4RawGapContribution ![0, 2, 8, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 8, 7] = b4GapPatternWeight 2 8 7 * 0 :=
      b4GapContribution_from_row 0 2 8 7 0 row_00_02_08_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_07

theorem row_00_02_08_08 : b4RowContribution (![0, 2, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 10, 18] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 10 + 18 = 30
    decide
  have hzsq : (∑ i, (((![0, 2, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 428 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 10^2 + 18^2 = 428
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_08_08

theorem weighted_00_02_08_08 : b4RawGapContribution ![0, 2, 8, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 8, 8] = b4GapPatternWeight 2 8 8 * 0 :=
      b4GapContribution_from_row 0 2 8 8 0 row_00_02_08_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_08

theorem row_00_02_08_09 : b4RowContribution (![0, 2, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 10, 19] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 10 + 19 = 31
    decide
  have hzsq : (∑ i, (((![0, 2, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 465 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 10^2 + 19^2 = 465
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_08_09

theorem weighted_00_02_08_09 : b4RawGapContribution ![0, 2, 8, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 8, 9] = b4GapPatternWeight 2 8 9 * 0 :=
      b4GapContribution_from_row 0 2 8 9 0 row_00_02_08_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_09

theorem row_00_02_08_10 : b4RowContribution (![0, 2, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 10, 20] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 10 + 20 = 32
    decide
  have hzsq : (∑ i, (((![0, 2, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 504 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 10^2 + 20^2 = 504
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_08_10

theorem weighted_00_02_08_10 : b4RawGapContribution ![0, 2, 8, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 8, 10] = b4GapPatternWeight 2 8 10 * 0 :=
      b4GapContribution_from_row 0 2 8 10 0 row_00_02_08_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_10

theorem row_00_02_08_11 : b4RowContribution (![0, 2, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 10, 21] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 10 + 21 = 33
    decide
  have hzsq : (∑ i, (((![0, 2, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 545 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 10^2 + 21^2 = 545
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_08_11

theorem weighted_00_02_08_11 : b4RawGapContribution ![0, 2, 8, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 8, 11] = b4GapPatternWeight 2 8 11 * 0 :=
      b4GapContribution_from_row 0 2 8 11 0 row_00_02_08_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_11

theorem row_00_02_08_12 : b4RowContribution (![0, 2, 10, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 10, 22] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 10 + 22 = 34
    decide
  have hzsq : (∑ i, (((![0, 2, 10, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 588 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 10^2 + 22^2 = 588
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_08_12

theorem weighted_00_02_08_12 : b4RawGapContribution ![0, 2, 8, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 8, 12] = b4GapPatternWeight 2 8 12 * 0 :=
      b4GapContribution_from_row 0 2 8 12 0 row_00_02_08_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_12

theorem row_00_02_08_13 : b4RowContribution (![0, 2, 10, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 10, 23] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 10 + 23 = 35
    decide
  have hzsq : (∑ i, (((![0, 2, 10, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 633 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 10^2 + 23^2 = 633
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_08_13

theorem weighted_00_02_08_13 : b4RawGapContribution ![0, 2, 8, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 8, 13] = b4GapPatternWeight 2 8 13 * 0 :=
      b4GapContribution_from_row 0 2 8 13 0 row_00_02_08_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_13

theorem row_00_02_08_14 : b4RowContribution (![0, 2, 10, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 10, 24] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 10 + 24 = 36
    decide
  have hzsq : (∑ i, (((![0, 2, 10, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 680 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 10^2 + 24^2 = 680
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_08_14

theorem weighted_00_02_08_14 : b4RawGapContribution ![0, 2, 8, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 8, 14] = b4GapPatternWeight 2 8 14 * 0 :=
      b4GapContribution_from_row 0 2 8 14 0 row_00_02_08_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_14

theorem row_00_02_08_15 : b4RowContribution (![0, 2, 10, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 10, 25] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 10 + 25 = 37
    decide
  have hzsq : (∑ i, (((![0, 2, 10, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 729 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 10^2 + 25^2 = 729
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_08_15

theorem weighted_00_02_08_15 : b4RawGapContribution ![0, 2, 8, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 8, 15] = b4GapPatternWeight 2 8 15 * 0 :=
      b4GapContribution_from_row 0 2 8 15 0 row_00_02_08_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_08_15

def dvalues_00_02_08 : Fin 16 → ℕ := ![0, 648, 0, 792, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_02_08

theorem dblock_00_02_08 : b4GapPatternDBlock 0 2 8 = 1440 := by
  calc
    b4GapPatternDBlock 0 2 8 = ∑ d : Fin 16, dvalues_00_02_08 d := by
      apply b4GapDBlock_of_rows 0 2 8 dvalues_00_02_08
      intro d
      fin_cases d
      · exact weighted_00_02_08_00
      · exact weighted_00_02_08_01
      · exact weighted_00_02_08_02
      · exact weighted_00_02_08_03
      · exact weighted_00_02_08_04
      · exact weighted_00_02_08_05
      · exact weighted_00_02_08_06
      · exact weighted_00_02_08_07
      · exact weighted_00_02_08_08
      · exact weighted_00_02_08_09
      · exact weighted_00_02_08_10
      · exact weighted_00_02_08_11
      · exact weighted_00_02_08_12
      · exact weighted_00_02_08_13
      · exact weighted_00_02_08_14
      · exact weighted_00_02_08_15
    _ = 1440 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_02_08

end Paper7MomentGapNumeric
