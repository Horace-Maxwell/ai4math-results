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

def layers_02_01_07_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 11, 12, 12, 12, 12, 12, 12, 11, 9, 6, 3, 1, 0, 0, 0], ![1, 4, 10, 19, 30, 42, 54, 66, 78, 90, 102, 112, 118, 118, 112, 102, 90, 78, 66]]
#print axioms Paper7MomentGapNumeric.layers_02_01_07_00

theorem cells_02_01_07_00 : QTableValid (![2, 3, 10, 10] : Fin 4 → ℕ) layers_02_01_07_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_07_00

theorem valid_02_01_07_00 :
    SparseRowValid (![2, 3, 10, 10] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_02_01_07_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 10, 10] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 10 + 10 = 25
      decide
    have hzsq : (∑ i, (((![2, 3, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 213 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 10^2 + 10^2 = 213
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_07_00
#print axioms Paper7MomentGapNumeric.valid_02_01_07_00

def qvalues_02_01_07_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 118, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_07_00

theorem row_02_01_07_00 : b4RowContribution (![2, 3, 10, 10] : Fin 4 → ℕ) = 118 := by
  calc
    b4RowContribution (![2, 3, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_02_01_07_00) :=
      sparseRow_sound (![2, 3, 10, 10] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_02_01_07_00) valid_02_01_07_00
    _ = 118 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_07_00 Q := by
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
        _ = 118 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_07_00

theorem weighted_02_01_07_00 : b4RawGapContribution ![2, 1, 7, 0] = 1416 := by
  calc
    b4RawGapContribution ![2, 1, 7, 0] = b4GapPatternWeight 1 7 0 * 118 :=
      b4GapContribution_from_row 2 1 7 0 118 row_02_01_07_00
    _ = 1416 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_07_00

def layers_02_01_07_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 11, 12, 12, 12, 12, 12, 12, 11, 9, 6, 3, 1, 0, 0, 0], ![1, 4, 10, 19, 30, 42, 54, 66, 78, 90, 102, 113, 121, 124, 121, 113, 102, 90, 78]]
#print axioms Paper7MomentGapNumeric.layers_02_01_07_01

theorem cells_02_01_07_01 : QTableValid (![2, 3, 10, 11] : Fin 4 → ℕ) layers_02_01_07_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_07_01

theorem valid_02_01_07_01 :
    SparseRowValid (![2, 3, 10, 11] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_02_01_07_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 10, 11] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 10 + 11 = 26
      decide
    have hzsq : (∑ i, (((![2, 3, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 234 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 10^2 + 11^2 = 234
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_07_01
#print axioms Paper7MomentGapNumeric.valid_02_01_07_01

def qvalues_02_01_07_01 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_07_01

theorem row_02_01_07_01 : b4RowContribution (![2, 3, 10, 11] : Fin 4 → ℕ) = 55 := by
  calc
    b4RowContribution (![2, 3, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_02_01_07_01) :=
      sparseRow_sound (![2, 3, 10, 11] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_02_01_07_01) valid_02_01_07_01
    _ = 55 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_07_01 Q := by
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
        _ = 55 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_07_01

theorem weighted_02_01_07_01 : b4RawGapContribution ![2, 1, 7, 1] = 1320 := by
  calc
    b4RawGapContribution ![2, 1, 7, 1] = b4GapPatternWeight 1 7 1 * 55 :=
      b4GapContribution_from_row 2 1 7 1 55 row_02_01_07_01
    _ = 1320 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_07_01

theorem row_02_01_07_02 : b4RowContribution (![2, 3, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 10, 12] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 10 + 12 = 27
    decide
  have hzsq : (∑ i, (((![2, 3, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 257 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 10^2 + 12^2 = 257
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_07_02

theorem weighted_02_01_07_02 : b4RawGapContribution ![2, 1, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 7, 2] = b4GapPatternWeight 1 7 2 * 0 :=
      b4GapContribution_from_row 2 1 7 2 0 row_02_01_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_07_02

def layers_02_01_07_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 11, 12, 12, 12, 12, 12, 12, 11, 9, 6, 3, 1, 0, 0, 0], ![1, 4, 10, 19, 30, 42, 54, 66, 78, 90, 102, 113, 122, 128, 130, 128, 122, 113, 102]]
#print axioms Paper7MomentGapNumeric.layers_02_01_07_03

theorem cells_02_01_07_03 : QTableValid (![2, 3, 10, 13] : Fin 4 → ℕ) layers_02_01_07_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_07_03

theorem valid_02_01_07_03 :
    SparseRowValid (![2, 3, 10, 13] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_02_01_07_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 10, 13] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 10 + 13 = 28
      decide
    have hzsq : (∑ i, (((![2, 3, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 282 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 10^2 + 13^2 = 282
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_07_03
#print axioms Paper7MomentGapNumeric.valid_02_01_07_03

def qvalues_02_01_07_03 : Fin 19 → ℕ := ![0, 0, 0, 19, 0, 0, 0, 0, 0, 90, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_07_03

theorem row_02_01_07_03 : b4RowContribution (![2, 3, 10, 13] : Fin 4 → ℕ) = 109 := by
  calc
    b4RowContribution (![2, 3, 10, 13] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9} : Finset (Fin 19)) (fun _ => layers_02_01_07_03) :=
      sparseRow_sound (![2, 3, 10, 13] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_02_01_07_03) valid_02_01_07_03
    _ = 109 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_07_03 Q := by
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
        _ = 109 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_07_03

theorem weighted_02_01_07_03 : b4RawGapContribution ![2, 1, 7, 3] = 2616 := by
  calc
    b4RawGapContribution ![2, 1, 7, 3] = b4GapPatternWeight 1 7 3 * 109 :=
      b4GapContribution_from_row 2 1 7 3 109 row_02_01_07_03
    _ = 2616 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_07_03

theorem row_02_01_07_04 : b4RowContribution (![2, 3, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 10, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 10 + 14 = 29
    decide
  have hzsq : (∑ i, (((![2, 3, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 309 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 10^2 + 14^2 = 309
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_07_04

theorem weighted_02_01_07_04 : b4RawGapContribution ![2, 1, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 7, 4] = b4GapPatternWeight 1 7 4 * 0 :=
      b4GapContribution_from_row 2 1 7 4 0 row_02_01_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_07_04

theorem row_02_01_07_05 : b4RowContribution (![2, 3, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 10, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 10 + 15 = 30
    decide
  have hzsq : (∑ i, (((![2, 3, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 338 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 10^2 + 15^2 = 338
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_07_05

theorem weighted_02_01_07_05 : b4RawGapContribution ![2, 1, 7, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 7, 5] = b4GapPatternWeight 1 7 5 * 0 :=
      b4GapContribution_from_row 2 1 7 5 0 row_02_01_07_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_07_05

theorem row_02_01_07_06 : b4RowContribution (![2, 3, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 10, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 10 + 16 = 31
    decide
  have hzsq : (∑ i, (((![2, 3, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 369 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 10^2 + 16^2 = 369
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_07_06

theorem weighted_02_01_07_06 : b4RawGapContribution ![2, 1, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 7, 6] = b4GapPatternWeight 1 7 6 * 0 :=
      b4GapContribution_from_row 2 1 7 6 0 row_02_01_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_07_06

theorem row_02_01_07_07 : b4RowContribution (![2, 3, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 10, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 10 + 17 = 32
    decide
  have hzsq : (∑ i, (((![2, 3, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 402 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 10^2 + 17^2 = 402
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_07_07

theorem weighted_02_01_07_07 : b4RawGapContribution ![2, 1, 7, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 7, 7] = b4GapPatternWeight 1 7 7 * 0 :=
      b4GapContribution_from_row 2 1 7 7 0 row_02_01_07_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_07_07

theorem row_02_01_07_08 : b4RowContribution (![2, 3, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 10, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 10 + 18 = 33
    decide
  have hzsq : (∑ i, (((![2, 3, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 437 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 10^2 + 18^2 = 437
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_07_08

theorem weighted_02_01_07_08 : b4RawGapContribution ![2, 1, 7, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 7, 8] = b4GapPatternWeight 1 7 8 * 0 :=
      b4GapContribution_from_row 2 1 7 8 0 row_02_01_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_07_08

theorem row_02_01_07_09 : b4RowContribution (![2, 3, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 10, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 10 + 19 = 34
    decide
  have hzsq : (∑ i, (((![2, 3, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 474 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 10^2 + 19^2 = 474
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_07_09

theorem weighted_02_01_07_09 : b4RawGapContribution ![2, 1, 7, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 7, 9] = b4GapPatternWeight 1 7 9 * 0 :=
      b4GapContribution_from_row 2 1 7 9 0 row_02_01_07_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_07_09

theorem row_02_01_07_10 : b4RowContribution (![2, 3, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 10, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 10 + 20 = 35
    decide
  have hzsq : (∑ i, (((![2, 3, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 513 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 10^2 + 20^2 = 513
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_07_10

theorem weighted_02_01_07_10 : b4RawGapContribution ![2, 1, 7, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 7, 10] = b4GapPatternWeight 1 7 10 * 0 :=
      b4GapContribution_from_row 2 1 7 10 0 row_02_01_07_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_07_10

theorem row_02_01_07_11 : b4RowContribution (![2, 3, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 10, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 10 + 21 = 36
    decide
  have hzsq : (∑ i, (((![2, 3, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 554 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 10^2 + 21^2 = 554
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_07_11

theorem weighted_02_01_07_11 : b4RawGapContribution ![2, 1, 7, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 7, 11] = b4GapPatternWeight 1 7 11 * 0 :=
      b4GapContribution_from_row 2 1 7 11 0 row_02_01_07_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_07_11

theorem row_02_01_07_12 : b4RowContribution (![2, 3, 10, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 10, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 10 + 22 = 37
    decide
  have hzsq : (∑ i, (((![2, 3, 10, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 597 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 10^2 + 22^2 = 597
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_07_12

theorem weighted_02_01_07_12 : b4RawGapContribution ![2, 1, 7, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 7, 12] = b4GapPatternWeight 1 7 12 * 0 :=
      b4GapContribution_from_row 2 1 7 12 0 row_02_01_07_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_07_12

def dvalues_02_01_07 : Fin 13 → ℕ := ![1416, 1320, 0, 2616, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_01_07

theorem dblock_02_01_07 : b4GapPatternDBlock 2 1 7 = 5352 := by
  calc
    b4GapPatternDBlock 2 1 7 = ∑ d : Fin 13, dvalues_02_01_07 d := by
      apply b4GapDBlock_of_rows 2 1 7 dvalues_02_01_07
      intro d
      fin_cases d
      · exact weighted_02_01_07_00
      · exact weighted_02_01_07_01
      · exact weighted_02_01_07_02
      · exact weighted_02_01_07_03
      · exact weighted_02_01_07_04
      · exact weighted_02_01_07_05
      · exact weighted_02_01_07_06
      · exact weighted_02_01_07_07
      · exact weighted_02_01_07_08
      · exact weighted_02_01_07_09
      · exact weighted_02_01_07_10
      · exact weighted_02_01_07_11
      · exact weighted_02_01_07_12
    _ = 5352 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_01_07

end Paper7MomentGapNumeric
