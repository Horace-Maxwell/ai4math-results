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

theorem row_00_03_06_00 : b4RowContribution (![0, 3, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 9] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 9 = 21
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 171 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 9^2 = 171
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_00

theorem weighted_00_03_06_00 : b4RawGapContribution ![0, 3, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 0] = b4GapPatternWeight 3 6 0 * 0 :=
      b4GapContribution_from_row 0 3 6 0 0 row_00_03_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_00

theorem row_00_03_06_01 : b4RowContribution (![0, 3, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 10] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 10 = 22
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 190 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 10^2 = 190
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_01

theorem weighted_00_03_06_01 : b4RawGapContribution ![0, 3, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 1] = b4GapPatternWeight 3 6 1 * 0 :=
      b4GapContribution_from_row 0 3 6 1 0 row_00_03_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_01

theorem row_00_03_06_02 : b4RowContribution (![0, 3, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 11] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 11 = 23
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 211 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 11^2 = 211
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_02

theorem weighted_00_03_06_02 : b4RawGapContribution ![0, 3, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 2] = b4GapPatternWeight 3 6 2 * 0 :=
      b4GapContribution_from_row 0 3 6 2 0 row_00_03_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_02

def layers_00_03_06_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 30, 34, 37, 39, 40, 39, 37, 34, 30, 26, 22]]
#print axioms Paper7MomentGapNumeric.layers_00_03_06_03

theorem cells_00_03_06_03 : QTableValid (![0, 3, 9, 12] : Fin 4 → ℕ) layers_00_03_06_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_06_03

theorem valid_00_03_06_03 :
    SparseRowValid (![0, 3, 9, 12] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_03_06_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 9, 12] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 9 + 12 = 24
      decide
    have hzsq : (∑ i, (((![0, 3, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 234 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 9^2 + 12^2 = 234
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_06_03
#print axioms Paper7MomentGapNumeric.valid_00_03_06_03

def qvalues_00_03_06_03 : Fin 19 → ℕ := ![0, 0, 0, 10, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_06_03

theorem row_00_03_06_03 : b4RowContribution (![0, 3, 9, 12] : Fin 4 → ℕ) = 44 := by
  calc
    b4RowContribution (![0, 3, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_03_06_03) :=
      sparseRow_sound (![0, 3, 9, 12] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_03_06_03) valid_00_03_06_03
    _ = 44 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_06_03 Q := by
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
        _ = 44 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_06_03

theorem weighted_00_03_06_03 : b4RawGapContribution ![0, 3, 6, 3] = 1056 := by
  calc
    b4RawGapContribution ![0, 3, 6, 3] = b4GapPatternWeight 3 6 3 * 44 :=
      b4GapContribution_from_row 0 3 6 3 44 row_00_03_06_03
    _ = 1056 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_03

theorem row_00_03_06_04 : b4RowContribution (![0, 3, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 13] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 13 = 25
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 259 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 13^2 = 259
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_04

theorem weighted_00_03_06_04 : b4RawGapContribution ![0, 3, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 4] = b4GapPatternWeight 3 6 4 * 0 :=
      b4GapContribution_from_row 0 3 6 4 0 row_00_03_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_04

def layers_00_03_06_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 30, 34, 37, 39, 40, 40, 40, 39, 37, 34, 30]]
#print axioms Paper7MomentGapNumeric.layers_00_03_06_05

theorem cells_00_03_06_05 : QTableValid (![0, 3, 9, 14] : Fin 4 → ℕ) layers_00_03_06_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_06_05

theorem valid_00_03_06_05 :
    SparseRowValid (![0, 3, 9, 14] : Fin 4 → ℕ) ({4, 10} : Finset (Fin 19)) (fun _ => layers_00_03_06_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 9, 14] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 9 + 14 = 26
      decide
    have hzsq : (∑ i, (((![0, 3, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 286 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 9^2 + 14^2 = 286
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_06_05
#print axioms Paper7MomentGapNumeric.valid_00_03_06_05

def qvalues_00_03_06_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_06_05

theorem row_00_03_06_05 : b4RowContribution (![0, 3, 9, 14] : Fin 4 → ℕ) = 51 := by
  calc
    b4RowContribution (![0, 3, 9, 14] : Fin 4 → ℕ) =
        sparseRowValue ({4, 10} : Finset (Fin 19)) (fun _ => layers_00_03_06_05) :=
      sparseRow_sound (![0, 3, 9, 14] : Fin 4 → ℕ) ({4, 10} : Finset (Fin 19)) (fun _ => layers_00_03_06_05) valid_00_03_06_05
    _ = 51 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_06_05 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 51 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_06_05

theorem weighted_00_03_06_05 : b4RawGapContribution ![0, 3, 6, 5] = 1224 := by
  calc
    b4RawGapContribution ![0, 3, 6, 5] = b4GapPatternWeight 3 6 5 * 51 :=
      b4GapContribution_from_row 0 3 6 5 51 row_00_03_06_05
    _ = 1224 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_05

theorem row_00_03_06_06 : b4RowContribution (![0, 3, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 15] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 15 = 27
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 315 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 15^2 = 315
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_06

theorem weighted_00_03_06_06 : b4RawGapContribution ![0, 3, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 6] = b4GapPatternWeight 3 6 6 * 0 :=
      b4GapContribution_from_row 0 3 6 6 0 row_00_03_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_06

theorem row_00_03_06_07 : b4RowContribution (![0, 3, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 16] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 16 = 28
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 346 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 16^2 = 346
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_07

theorem weighted_00_03_06_07 : b4RawGapContribution ![0, 3, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 7] = b4GapPatternWeight 3 6 7 * 0 :=
      b4GapContribution_from_row 0 3 6 7 0 row_00_03_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_07

theorem row_00_03_06_08 : b4RowContribution (![0, 3, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 17] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 17 = 29
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 379 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 17^2 = 379
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_08

theorem weighted_00_03_06_08 : b4RawGapContribution ![0, 3, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 8] = b4GapPatternWeight 3 6 8 * 0 :=
      b4GapContribution_from_row 0 3 6 8 0 row_00_03_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_08

theorem row_00_03_06_09 : b4RowContribution (![0, 3, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 18] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 18 = 30
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 414 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 18^2 = 414
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_09

theorem weighted_00_03_06_09 : b4RawGapContribution ![0, 3, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 9] = b4GapPatternWeight 3 6 9 * 0 :=
      b4GapContribution_from_row 0 3 6 9 0 row_00_03_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_09

theorem row_00_03_06_10 : b4RowContribution (![0, 3, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 19] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 19 = 31
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 451 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 19^2 = 451
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_10

theorem weighted_00_03_06_10 : b4RawGapContribution ![0, 3, 6, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 10] = b4GapPatternWeight 3 6 10 * 0 :=
      b4GapContribution_from_row 0 3 6 10 0 row_00_03_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_10

theorem row_00_03_06_11 : b4RowContribution (![0, 3, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 20] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 20 = 32
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 490 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 20^2 = 490
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_11

theorem weighted_00_03_06_11 : b4RawGapContribution ![0, 3, 6, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 11] = b4GapPatternWeight 3 6 11 * 0 :=
      b4GapContribution_from_row 0 3 6 11 0 row_00_03_06_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_11

theorem row_00_03_06_12 : b4RowContribution (![0, 3, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 21] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 21 = 33
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 531 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 21^2 = 531
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_12

theorem weighted_00_03_06_12 : b4RawGapContribution ![0, 3, 6, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 12] = b4GapPatternWeight 3 6 12 * 0 :=
      b4GapContribution_from_row 0 3 6 12 0 row_00_03_06_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_12

theorem row_00_03_06_13 : b4RowContribution (![0, 3, 9, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 22] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 22 = 34
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 574 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 22^2 = 574
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_13

theorem weighted_00_03_06_13 : b4RawGapContribution ![0, 3, 6, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 13] = b4GapPatternWeight 3 6 13 * 0 :=
      b4GapContribution_from_row 0 3 6 13 0 row_00_03_06_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_13

theorem row_00_03_06_14 : b4RowContribution (![0, 3, 9, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 23] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 23 = 35
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 619 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 23^2 = 619
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_14

theorem weighted_00_03_06_14 : b4RawGapContribution ![0, 3, 6, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 14] = b4GapPatternWeight 3 6 14 * 0 :=
      b4GapContribution_from_row 0 3 6 14 0 row_00_03_06_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_14

theorem row_00_03_06_15 : b4RowContribution (![0, 3, 9, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 24] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 24 = 36
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 666 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 24^2 = 666
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_15

theorem weighted_00_03_06_15 : b4RawGapContribution ![0, 3, 6, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 15] = b4GapPatternWeight 3 6 15 * 0 :=
      b4GapContribution_from_row 0 3 6 15 0 row_00_03_06_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_15

theorem row_00_03_06_16 : b4RowContribution (![0, 3, 9, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 9, 25] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 9 + 25 = 37
    decide
  have hzsq : (∑ i, (((![0, 3, 9, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 715 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 9^2 + 25^2 = 715
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_06_16

theorem weighted_00_03_06_16 : b4RawGapContribution ![0, 3, 6, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 6, 16] = b4GapPatternWeight 3 6 16 * 0 :=
      b4GapContribution_from_row 0 3 6 16 0 row_00_03_06_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_06_16

def dvalues_00_03_06 : Fin 17 → ℕ := ![0, 0, 0, 1056, 0, 1224, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_03_06

theorem dblock_00_03_06 : b4GapPatternDBlock 0 3 6 = 2280 := by
  calc
    b4GapPatternDBlock 0 3 6 = ∑ d : Fin 17, dvalues_00_03_06 d := by
      apply b4GapDBlock_of_rows 0 3 6 dvalues_00_03_06
      intro d
      fin_cases d
      · exact weighted_00_03_06_00
      · exact weighted_00_03_06_01
      · exact weighted_00_03_06_02
      · exact weighted_00_03_06_03
      · exact weighted_00_03_06_04
      · exact weighted_00_03_06_05
      · exact weighted_00_03_06_06
      · exact weighted_00_03_06_07
      · exact weighted_00_03_06_08
      · exact weighted_00_03_06_09
      · exact weighted_00_03_06_10
      · exact weighted_00_03_06_11
      · exact weighted_00_03_06_12
      · exact weighted_00_03_06_13
      · exact weighted_00_03_06_14
      · exact weighted_00_03_06_15
      · exact weighted_00_03_06_16
    _ = 2280 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_03_06

end Paper7MomentGapNumeric
