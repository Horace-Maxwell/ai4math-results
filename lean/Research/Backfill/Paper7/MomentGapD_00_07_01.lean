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

theorem row_00_07_01_00 : b4RowContribution (![0, 7, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 8, 8] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 8 + 8 = 23
    decide
  have hzsq : (∑ i, (((![0, 7, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 177 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 8^2 + 8^2 = 177
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_01_00

theorem weighted_00_07_01_00 : b4RawGapContribution ![0, 7, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 1, 0] = b4GapPatternWeight 7 1 0 * 0 :=
      b4GapContribution_from_row 0 7 1 0 0 row_00_07_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_00

theorem row_00_07_01_01 : b4RowContribution (![0, 7, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 8, 9] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 8 + 9 = 24
    decide
  have hzsq : (∑ i, (((![0, 7, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 194 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 8^2 + 9^2 = 194
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_01_01

theorem weighted_00_07_01_01 : b4RawGapContribution ![0, 7, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 1, 1] = b4GapPatternWeight 7 1 1 * 0 :=
      b4GapContribution_from_row 0 7 1 1 0 row_00_07_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_01

def layers_00_07_01_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 36, 44, 51, 57, 61, 63, 63, 61, 57, 51, 44, 36]]
#print axioms Paper7MomentGapNumeric.layers_00_07_01_02

theorem cells_00_07_01_02 : QTableValid (![0, 7, 8, 10] : Fin 4 → ℕ) layers_00_07_01_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_07_01_02

theorem valid_00_07_01_02 :
    SparseRowValid (![0, 7, 8, 10] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_07_01_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 7, 8, 10] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 7 + 8 + 10 = 25
      decide
    have hzsq : (∑ i, (((![0, 7, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 213 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 7^2 + 8^2 + 10^2 = 213
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_07_01_02
#print axioms Paper7MomentGapNumeric.valid_00_07_01_02

def qvalues_00_07_01_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 63, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_07_01_02

theorem row_00_07_01_02 : b4RowContribution (![0, 7, 8, 10] : Fin 4 → ℕ) = 63 := by
  calc
    b4RowContribution (![0, 7, 8, 10] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_00_07_01_02) :=
      sparseRow_sound (![0, 7, 8, 10] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_07_01_02) valid_00_07_01_02
    _ = 63 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_07_01_02 Q := by
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
        _ = 63 := by decide
#print axioms Paper7MomentGapNumeric.row_00_07_01_02

theorem weighted_00_07_01_02 : b4RawGapContribution ![0, 7, 1, 2] = 1512 := by
  calc
    b4RawGapContribution ![0, 7, 1, 2] = b4GapPatternWeight 7 1 2 * 63 :=
      b4GapContribution_from_row 0 7 1 2 63 row_00_07_01_02
    _ = 1512 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_02

def layers_00_07_01_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 36, 44, 51, 57, 62, 65, 66, 65, 62, 57, 51, 44]]
#print axioms Paper7MomentGapNumeric.layers_00_07_01_03

theorem cells_00_07_01_03 : QTableValid (![0, 7, 8, 11] : Fin 4 → ℕ) layers_00_07_01_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_07_01_03

theorem valid_00_07_01_03 :
    SparseRowValid (![0, 7, 8, 11] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_00_07_01_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 7, 8, 11] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 0 + 7 + 8 + 11 = 26
      decide
    have hzsq : (∑ i, (((![0, 7, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 234 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 7^2 + 8^2 + 11^2 = 234
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_07_01_03
#print axioms Paper7MomentGapNumeric.valid_00_07_01_03

def qvalues_00_07_01_03 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_07_01_03

theorem row_00_07_01_03 : b4RowContribution (![0, 7, 8, 11] : Fin 4 → ℕ) = 29 := by
  calc
    b4RowContribution (![0, 7, 8, 11] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_00_07_01_03) :=
      sparseRow_sound (![0, 7, 8, 11] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_00_07_01_03) valid_00_07_01_03
    _ = 29 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_07_01_03 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 29 := by decide
#print axioms Paper7MomentGapNumeric.row_00_07_01_03

theorem weighted_00_07_01_03 : b4RawGapContribution ![0, 7, 1, 3] = 696 := by
  calc
    b4RawGapContribution ![0, 7, 1, 3] = b4GapPatternWeight 7 1 3 * 29 :=
      b4GapContribution_from_row 0 7 1 3 29 row_00_07_01_03
    _ = 696 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_03

theorem row_00_07_01_04 : b4RowContribution (![0, 7, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 8, 12] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 8 + 12 = 27
    decide
  have hzsq : (∑ i, (((![0, 7, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 257 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 8^2 + 12^2 = 257
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_01_04

theorem weighted_00_07_01_04 : b4RawGapContribution ![0, 7, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 1, 4] = b4GapPatternWeight 7 1 4 * 0 :=
      b4GapContribution_from_row 0 7 1 4 0 row_00_07_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_04

def layers_00_07_01_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 36, 44, 51, 57, 62, 66, 69, 70, 69, 66, 62, 57]]
#print axioms Paper7MomentGapNumeric.layers_00_07_01_05

theorem cells_00_07_01_05 : QTableValid (![0, 7, 8, 13] : Fin 4 → ℕ) layers_00_07_01_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_07_01_05

theorem valid_00_07_01_05 :
    SparseRowValid (![0, 7, 8, 13] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_07_01_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 7, 8, 13] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 0 + 7 + 8 + 13 = 28
      decide
    have hzsq : (∑ i, (((![0, 7, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 282 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 7^2 + 8^2 + 13^2 = 282
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_07_01_05
#print axioms Paper7MomentGapNumeric.valid_00_07_01_05

def qvalues_00_07_01_05 : Fin 19 → ℕ := ![0, 0, 0, 10, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_07_01_05

theorem row_00_07_01_05 : b4RowContribution (![0, 7, 8, 13] : Fin 4 → ℕ) = 61 := by
  calc
    b4RowContribution (![0, 7, 8, 13] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_07_01_05) :=
      sparseRow_sound (![0, 7, 8, 13] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_07_01_05) valid_00_07_01_05
    _ = 61 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_07_01_05 Q := by
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
        _ = 61 := by decide
#print axioms Paper7MomentGapNumeric.row_00_07_01_05

theorem weighted_00_07_01_05 : b4RawGapContribution ![0, 7, 1, 5] = 1464 := by
  calc
    b4RawGapContribution ![0, 7, 1, 5] = b4GapPatternWeight 7 1 5 * 61 :=
      b4GapContribution_from_row 0 7 1 5 61 row_00_07_01_05
    _ = 1464 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_05

theorem row_00_07_01_06 : b4RowContribution (![0, 7, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 8, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 8 + 14 = 29
    decide
  have hzsq : (∑ i, (((![0, 7, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 309 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 8^2 + 14^2 = 309
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_01_06

theorem weighted_00_07_01_06 : b4RawGapContribution ![0, 7, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 1, 6] = b4GapPatternWeight 7 1 6 * 0 :=
      b4GapContribution_from_row 0 7 1 6 0 row_00_07_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_06

theorem row_00_07_01_07 : b4RowContribution (![0, 7, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 8, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 8 + 15 = 30
    decide
  have hzsq : (∑ i, (((![0, 7, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 338 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 8^2 + 15^2 = 338
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_01_07

theorem weighted_00_07_01_07 : b4RawGapContribution ![0, 7, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 1, 7] = b4GapPatternWeight 7 1 7 * 0 :=
      b4GapContribution_from_row 0 7 1 7 0 row_00_07_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_07

theorem row_00_07_01_08 : b4RowContribution (![0, 7, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 8, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 8 + 16 = 31
    decide
  have hzsq : (∑ i, (((![0, 7, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 369 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 8^2 + 16^2 = 369
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_01_08

theorem weighted_00_07_01_08 : b4RawGapContribution ![0, 7, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 1, 8] = b4GapPatternWeight 7 1 8 * 0 :=
      b4GapContribution_from_row 0 7 1 8 0 row_00_07_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_08

theorem row_00_07_01_09 : b4RowContribution (![0, 7, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 8, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 8 + 17 = 32
    decide
  have hzsq : (∑ i, (((![0, 7, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 402 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 8^2 + 17^2 = 402
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_01_09

theorem weighted_00_07_01_09 : b4RawGapContribution ![0, 7, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 1, 9] = b4GapPatternWeight 7 1 9 * 0 :=
      b4GapContribution_from_row 0 7 1 9 0 row_00_07_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_09

theorem row_00_07_01_10 : b4RowContribution (![0, 7, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 8, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 8 + 18 = 33
    decide
  have hzsq : (∑ i, (((![0, 7, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 437 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 8^2 + 18^2 = 437
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_01_10

theorem weighted_00_07_01_10 : b4RawGapContribution ![0, 7, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 1, 10] = b4GapPatternWeight 7 1 10 * 0 :=
      b4GapContribution_from_row 0 7 1 10 0 row_00_07_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_10

theorem row_00_07_01_11 : b4RowContribution (![0, 7, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 8, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 8 + 19 = 34
    decide
  have hzsq : (∑ i, (((![0, 7, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 474 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 8^2 + 19^2 = 474
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_01_11

theorem weighted_00_07_01_11 : b4RawGapContribution ![0, 7, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 1, 11] = b4GapPatternWeight 7 1 11 * 0 :=
      b4GapContribution_from_row 0 7 1 11 0 row_00_07_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_11

theorem row_00_07_01_12 : b4RowContribution (![0, 7, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 8, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 8 + 20 = 35
    decide
  have hzsq : (∑ i, (((![0, 7, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 513 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 8^2 + 20^2 = 513
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_01_12

theorem weighted_00_07_01_12 : b4RawGapContribution ![0, 7, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 1, 12] = b4GapPatternWeight 7 1 12 * 0 :=
      b4GapContribution_from_row 0 7 1 12 0 row_00_07_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_12

theorem row_00_07_01_13 : b4RowContribution (![0, 7, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 8, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 8 + 21 = 36
    decide
  have hzsq : (∑ i, (((![0, 7, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 554 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 8^2 + 21^2 = 554
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_01_13

theorem weighted_00_07_01_13 : b4RawGapContribution ![0, 7, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 1, 13] = b4GapPatternWeight 7 1 13 * 0 :=
      b4GapContribution_from_row 0 7 1 13 0 row_00_07_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_13

theorem row_00_07_01_14 : b4RowContribution (![0, 7, 8, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 8, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 8 + 22 = 37
    decide
  have hzsq : (∑ i, (((![0, 7, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 597 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 8^2 + 22^2 = 597
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_01_14

theorem weighted_00_07_01_14 : b4RawGapContribution ![0, 7, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 1, 14] = b4GapPatternWeight 7 1 14 * 0 :=
      b4GapContribution_from_row 0 7 1 14 0 row_00_07_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_01_14

def dvalues_00_07_01 : Fin 15 → ℕ := ![0, 0, 1512, 696, 0, 1464, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_07_01

theorem dblock_00_07_01 : b4GapPatternDBlock 0 7 1 = 3672 := by
  calc
    b4GapPatternDBlock 0 7 1 = ∑ d : Fin 15, dvalues_00_07_01 d := by
      apply b4GapDBlock_of_rows 0 7 1 dvalues_00_07_01
      intro d
      fin_cases d
      · exact weighted_00_07_01_00
      · exact weighted_00_07_01_01
      · exact weighted_00_07_01_02
      · exact weighted_00_07_01_03
      · exact weighted_00_07_01_04
      · exact weighted_00_07_01_05
      · exact weighted_00_07_01_06
      · exact weighted_00_07_01_07
      · exact weighted_00_07_01_08
      · exact weighted_00_07_01_09
      · exact weighted_00_07_01_10
      · exact weighted_00_07_01_11
      · exact weighted_00_07_01_12
      · exact weighted_00_07_01_13
      · exact weighted_00_07_01_14
    _ = 3672 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_07_01

end Paper7MomentGapNumeric
