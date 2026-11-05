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

theorem row_02_00_07_00 : b4RowContribution (![2, 2, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 9, 9] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 9 + 9 = 22
    decide
  have hzsq : (∑ i, (((![2, 2, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 170 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 9^2 + 9^2 = 170
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_07_00

theorem weighted_02_00_07_00 : b4RawGapContribution ![2, 0, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 7, 0] = b4GapPatternWeight 0 7 0 * 0 :=
      b4GapContribution_from_row 2 0 7 0 0 row_02_00_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_00

theorem row_02_00_07_01 : b4RowContribution (![2, 2, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 9, 10] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 9 + 10 = 23
    decide
  have hzsq : (∑ i, (((![2, 2, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 189 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 9^2 + 10^2 = 189
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_07_01

theorem weighted_02_00_07_01 : b4RawGapContribution ![2, 0, 7, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 7, 1] = b4GapPatternWeight 0 7 1 * 0 :=
      b4GapContribution_from_row 2 0 7 1 0 row_02_00_07_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_01

theorem row_02_00_07_02 : b4RowContribution (![2, 2, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 9, 11] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 9 + 11 = 24
    decide
  have hzsq : (∑ i, (((![2, 2, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 210 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 9^2 + 11^2 = 210
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_07_02

theorem weighted_02_00_07_02 : b4RawGapContribution ![2, 0, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 7, 2] = b4GapPatternWeight 0 7 2 * 0 :=
      b4GapContribution_from_row 2 0 7 2 0 row_02_00_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_02

def layers_02_00_07_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 9, 9, 9, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 36, 45, 54, 63, 72, 80, 86, 89, 89, 86, 80, 72, 63, 54]]
#print axioms Paper7MomentGapNumeric.layers_02_00_07_03

theorem cells_02_00_07_03 : QTableValid (![2, 2, 9, 12] : Fin 4 → ℕ) layers_02_00_07_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_07_03

theorem valid_02_00_07_03 :
    SparseRowValid (![2, 2, 9, 12] : Fin 4 → ℕ) ({2, 8} : Finset (Fin 19)) (fun _ => layers_02_00_07_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 9, 12] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 9 + 12 = 25
      decide
    have hzsq : (∑ i, (((![2, 2, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 233 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 9^2 + 12^2 = 233
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_07_03
#print axioms Paper7MomentGapNumeric.valid_02_00_07_03

def qvalues_02_00_07_03 : Fin 19 → ℕ := ![0, 0, 10, 0, 0, 0, 0, 0, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_07_03

theorem row_02_00_07_03 : b4RowContribution (![2, 2, 9, 12] : Fin 4 → ℕ) = 73 := by
  calc
    b4RowContribution (![2, 2, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({2, 8} : Finset (Fin 19)) (fun _ => layers_02_00_07_03) :=
      sparseRow_sound (![2, 2, 9, 12] : Fin 4 → ℕ) ({2, 8} : Finset (Fin 19)) (fun _ => layers_02_00_07_03) valid_02_00_07_03
    _ = 73 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_07_03 Q := by
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
        _ = 73 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_07_03

theorem weighted_02_00_07_03 : b4RawGapContribution ![2, 0, 7, 3] = 876 := by
  calc
    b4RawGapContribution ![2, 0, 7, 3] = b4GapPatternWeight 0 7 3 * 73 :=
      b4GapContribution_from_row 2 0 7 3 73 row_02_00_07_03
    _ = 876 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_03

theorem row_02_00_07_04 : b4RowContribution (![2, 2, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 9, 13] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 9 + 13 = 26
    decide
  have hzsq : (∑ i, (((![2, 2, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 258 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 9^2 + 13^2 = 258
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_07_04

theorem weighted_02_00_07_04 : b4RawGapContribution ![2, 0, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 7, 4] = b4GapPatternWeight 0 7 4 * 0 :=
      b4GapContribution_from_row 2 0 7 4 0 row_02_00_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_04

def layers_02_00_07_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 9, 9, 9, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 36, 45, 54, 63, 72, 80, 86, 89, 90, 90, 89, 86, 80, 72]]
#print axioms Paper7MomentGapNumeric.layers_02_00_07_05

theorem cells_02_00_07_05 : QTableValid (![2, 2, 9, 14] : Fin 4 → ℕ) layers_02_00_07_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_07_05

theorem valid_02_00_07_05 :
    SparseRowValid (![2, 2, 9, 14] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_02_00_07_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 9, 14] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 9 + 14 = 27
      decide
    have hzsq : (∑ i, (((![2, 2, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 285 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 9^2 + 14^2 = 285
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_07_05
#print axioms Paper7MomentGapNumeric.valid_02_00_07_05

def qvalues_02_00_07_05 : Fin 19 → ℕ := ![0, 0, 0, 18, 0, 0, 0, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_07_05

theorem row_02_00_07_05 : b4RowContribution (![2, 2, 9, 14] : Fin 4 → ℕ) = 90 := by
  calc
    b4RowContribution (![2, 2, 9, 14] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9} : Finset (Fin 19)) (fun _ => layers_02_00_07_05) :=
      sparseRow_sound (![2, 2, 9, 14] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_02_00_07_05) valid_02_00_07_05
    _ = 90 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_07_05 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
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
        _ = 90 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_07_05

theorem weighted_02_00_07_05 : b4RawGapContribution ![2, 0, 7, 5] = 1080 := by
  calc
    b4RawGapContribution ![2, 0, 7, 5] = b4GapPatternWeight 0 7 5 * 90 :=
      b4GapContribution_from_row 2 0 7 5 90 row_02_00_07_05
    _ = 1080 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_05

theorem row_02_00_07_06 : b4RowContribution (![2, 2, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 9, 15] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 9 + 15 = 28
    decide
  have hzsq : (∑ i, (((![2, 2, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 314 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 9^2 + 15^2 = 314
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_07_06

theorem weighted_02_00_07_06 : b4RawGapContribution ![2, 0, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 7, 6] = b4GapPatternWeight 0 7 6 * 0 :=
      b4GapContribution_from_row 2 0 7 6 0 row_02_00_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_06

theorem row_02_00_07_07 : b4RowContribution (![2, 2, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 9, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 9 + 16 = 29
    decide
  have hzsq : (∑ i, (((![2, 2, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 345 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 9^2 + 16^2 = 345
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_07_07

theorem weighted_02_00_07_07 : b4RawGapContribution ![2, 0, 7, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 7, 7] = b4GapPatternWeight 0 7 7 * 0 :=
      b4GapContribution_from_row 2 0 7 7 0 row_02_00_07_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_07

theorem row_02_00_07_08 : b4RowContribution (![2, 2, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 9, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 9 + 17 = 30
    decide
  have hzsq : (∑ i, (((![2, 2, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 378 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 9^2 + 17^2 = 378
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_07_08

theorem weighted_02_00_07_08 : b4RawGapContribution ![2, 0, 7, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 7, 8] = b4GapPatternWeight 0 7 8 * 0 :=
      b4GapContribution_from_row 2 0 7 8 0 row_02_00_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_08

theorem row_02_00_07_09 : b4RowContribution (![2, 2, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 9, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 9 + 18 = 31
    decide
  have hzsq : (∑ i, (((![2, 2, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 413 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 9^2 + 18^2 = 413
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_07_09

theorem weighted_02_00_07_09 : b4RawGapContribution ![2, 0, 7, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 7, 9] = b4GapPatternWeight 0 7 9 * 0 :=
      b4GapContribution_from_row 2 0 7 9 0 row_02_00_07_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_09

theorem row_02_00_07_10 : b4RowContribution (![2, 2, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 9, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 9 + 19 = 32
    decide
  have hzsq : (∑ i, (((![2, 2, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 9^2 + 19^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_07_10

theorem weighted_02_00_07_10 : b4RawGapContribution ![2, 0, 7, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 7, 10] = b4GapPatternWeight 0 7 10 * 0 :=
      b4GapContribution_from_row 2 0 7 10 0 row_02_00_07_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_10

theorem row_02_00_07_11 : b4RowContribution (![2, 2, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 9, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 9 + 20 = 33
    decide
  have hzsq : (∑ i, (((![2, 2, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 489 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 9^2 + 20^2 = 489
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_07_11

theorem weighted_02_00_07_11 : b4RawGapContribution ![2, 0, 7, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 7, 11] = b4GapPatternWeight 0 7 11 * 0 :=
      b4GapContribution_from_row 2 0 7 11 0 row_02_00_07_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_11

theorem row_02_00_07_12 : b4RowContribution (![2, 2, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 9, 21] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 9 + 21 = 34
    decide
  have hzsq : (∑ i, (((![2, 2, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 530 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 9^2 + 21^2 = 530
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_07_12

theorem weighted_02_00_07_12 : b4RawGapContribution ![2, 0, 7, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 7, 12] = b4GapPatternWeight 0 7 12 * 0 :=
      b4GapContribution_from_row 2 0 7 12 0 row_02_00_07_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_12

theorem row_02_00_07_13 : b4RowContribution (![2, 2, 9, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 9, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 9 + 22 = 35
    decide
  have hzsq : (∑ i, (((![2, 2, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 573 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 9^2 + 22^2 = 573
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_07_13

theorem weighted_02_00_07_13 : b4RawGapContribution ![2, 0, 7, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 7, 13] = b4GapPatternWeight 0 7 13 * 0 :=
      b4GapContribution_from_row 2 0 7 13 0 row_02_00_07_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_13

theorem row_02_00_07_14 : b4RowContribution (![2, 2, 9, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 9, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 9 + 23 = 36
    decide
  have hzsq : (∑ i, (((![2, 2, 9, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 618 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 9^2 + 23^2 = 618
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_07_14

theorem weighted_02_00_07_14 : b4RawGapContribution ![2, 0, 7, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 7, 14] = b4GapPatternWeight 0 7 14 * 0 :=
      b4GapContribution_from_row 2 0 7 14 0 row_02_00_07_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_14

theorem row_02_00_07_15 : b4RowContribution (![2, 2, 9, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 9, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 9 + 24 = 37
    decide
  have hzsq : (∑ i, (((![2, 2, 9, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 665 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 9^2 + 24^2 = 665
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_07_15

theorem weighted_02_00_07_15 : b4RawGapContribution ![2, 0, 7, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 7, 15] = b4GapPatternWeight 0 7 15 * 0 :=
      b4GapContribution_from_row 2 0 7 15 0 row_02_00_07_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_07_15

def dvalues_02_00_07 : Fin 16 → ℕ := ![0, 0, 0, 876, 0, 1080, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_00_07

theorem dblock_02_00_07 : b4GapPatternDBlock 2 0 7 = 1956 := by
  calc
    b4GapPatternDBlock 2 0 7 = ∑ d : Fin 16, dvalues_02_00_07 d := by
      apply b4GapDBlock_of_rows 2 0 7 dvalues_02_00_07
      intro d
      fin_cases d
      · exact weighted_02_00_07_00
      · exact weighted_02_00_07_01
      · exact weighted_02_00_07_02
      · exact weighted_02_00_07_03
      · exact weighted_02_00_07_04
      · exact weighted_02_00_07_05
      · exact weighted_02_00_07_06
      · exact weighted_02_00_07_07
      · exact weighted_02_00_07_08
      · exact weighted_02_00_07_09
      · exact weighted_02_00_07_10
      · exact weighted_02_00_07_11
      · exact weighted_02_00_07_12
      · exact weighted_02_00_07_13
      · exact weighted_02_00_07_14
      · exact weighted_02_00_07_15
    _ = 1956 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_00_07

end Paper7MomentGapNumeric
