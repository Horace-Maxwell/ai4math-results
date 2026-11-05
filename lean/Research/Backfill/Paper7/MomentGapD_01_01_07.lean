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

theorem row_01_01_07_00 : b4RowContribution (![1, 2, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 9, 9] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 9 + 9 = 21
    decide
  have hzsq : (∑ i, (((![1, 2, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 167 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 9^2 + 9^2 = 167
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_07_00

theorem weighted_01_01_07_00 : b4RawGapContribution ![1, 1, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 7, 0] = b4GapPatternWeight 1 7 0 * 0 :=
      b4GapContribution_from_row 1 1 7 0 0 row_01_01_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_00

def layers_01_01_07_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 27, 33, 39, 45, 51, 56, 58, 56, 51, 45, 39, 33, 27, 21]]
#print axioms Paper7MomentGapNumeric.layers_01_01_07_01

theorem cells_01_01_07_01 : QTableValid (![1, 2, 9, 10] : Fin 4 → ℕ) layers_01_01_07_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_07_01

theorem valid_01_01_07_01 :
    SparseRowValid (![1, 2, 9, 10] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_01_01_07_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 9, 10] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 9 + 10 = 22
      decide
    have hzsq : (∑ i, (((![1, 2, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 186 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 9^2 + 10^2 = 186
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_07_01
#print axioms Paper7MomentGapNumeric.valid_01_01_07_01

def qvalues_01_01_07_01 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_07_01

theorem row_01_01_07_01 : b4RowContribution (![1, 2, 9, 10] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![1, 2, 9, 10] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_01_01_07_01) :=
      sparseRow_sound (![1, 2, 9, 10] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_01_01_07_01) valid_01_01_07_01
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_07_01 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_01_07_01

theorem weighted_01_01_07_01 : b4RawGapContribution ![1, 1, 7, 1] = 24 := by
  calc
    b4RawGapContribution ![1, 1, 7, 1] = b4GapPatternWeight 1 7 1 * 1 :=
      b4GapContribution_from_row 1 1 7 1 1 row_01_01_07_01
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_01

theorem row_01_01_07_02 : b4RowContribution (![1, 2, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 9, 11] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 9 + 11 = 23
    decide
  have hzsq : (∑ i, (((![1, 2, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 207 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 9^2 + 11^2 = 207
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_07_02

theorem weighted_01_01_07_02 : b4RawGapContribution ![1, 1, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 7, 2] = b4GapPatternWeight 1 7 2 * 0 :=
      b4GapContribution_from_row 1 1 7 2 0 row_01_01_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_02

def layers_01_01_07_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 27, 33, 39, 45, 51, 56, 59, 60, 59, 56, 51, 45, 39, 33]]
#print axioms Paper7MomentGapNumeric.layers_01_01_07_03

theorem cells_01_01_07_03 : QTableValid (![1, 2, 9, 12] : Fin 4 → ℕ) layers_01_01_07_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_07_03

theorem valid_01_01_07_03 :
    SparseRowValid (![1, 2, 9, 12] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_01_01_07_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 9, 12] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 9 + 12 = 24
      decide
    have hzsq : (∑ i, (((![1, 2, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 230 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 9^2 + 12^2 = 230
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_07_03
#print axioms Paper7MomentGapNumeric.valid_01_01_07_03

def qvalues_01_01_07_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 59, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_07_03

theorem row_01_01_07_03 : b4RowContribution (![1, 2, 9, 12] : Fin 4 → ℕ) = 86 := by
  calc
    b4RowContribution (![1, 2, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({5, 11} : Finset (Fin 19)) (fun _ => layers_01_01_07_03) :=
      sparseRow_sound (![1, 2, 9, 12] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_01_01_07_03) valid_01_01_07_03
    _ = 86 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_07_03 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 86 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_07_03

theorem weighted_01_01_07_03 : b4RawGapContribution ![1, 1, 7, 3] = 2064 := by
  calc
    b4RawGapContribution ![1, 1, 7, 3] = b4GapPatternWeight 1 7 3 * 86 :=
      b4GapContribution_from_row 1 1 7 3 86 row_01_01_07_03
    _ = 2064 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_03

theorem row_01_01_07_04 : b4RowContribution (![1, 2, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 9, 13] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 9 + 13 = 25
    decide
  have hzsq : (∑ i, (((![1, 2, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 255 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 9^2 + 13^2 = 255
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_07_04

theorem weighted_01_01_07_04 : b4RawGapContribution ![1, 1, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 7, 4] = b4GapPatternWeight 1 7 4 * 0 :=
      b4GapContribution_from_row 1 1 7 4 0 row_01_01_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_04

def layers_01_01_07_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 27, 33, 39, 45, 51, 56, 59, 60, 60, 60, 59, 56, 51, 45]]
#print axioms Paper7MomentGapNumeric.layers_01_01_07_05

theorem cells_01_01_07_05 : QTableValid (![1, 2, 9, 14] : Fin 4 → ℕ) layers_01_01_07_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_07_05

theorem valid_01_01_07_05 :
    SparseRowValid (![1, 2, 9, 14] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_01_01_07_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 9, 14] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 9 + 14 = 26
      decide
    have hzsq : (∑ i, (((![1, 2, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 282 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 9^2 + 14^2 = 282
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_07_05
#print axioms Paper7MomentGapNumeric.valid_01_01_07_05

def qvalues_01_01_07_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_07_05

theorem row_01_01_07_05 : b4RowContribution (![1, 2, 9, 14] : Fin 4 → ℕ) = 33 := by
  calc
    b4RowContribution (![1, 2, 9, 14] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_01_01_07_05) :=
      sparseRow_sound (![1, 2, 9, 14] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_01_01_07_05) valid_01_01_07_05
    _ = 33 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_07_05 Q := by
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
        _ = 33 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_07_05

theorem weighted_01_01_07_05 : b4RawGapContribution ![1, 1, 7, 5] = 792 := by
  calc
    b4RawGapContribution ![1, 1, 7, 5] = b4GapPatternWeight 1 7 5 * 33 :=
      b4GapContribution_from_row 1 1 7 5 33 row_01_01_07_05
    _ = 792 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_05

theorem row_01_01_07_06 : b4RowContribution (![1, 2, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 9, 15] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 9 + 15 = 27
    decide
  have hzsq : (∑ i, (((![1, 2, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 311 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 9^2 + 15^2 = 311
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_07_06

theorem weighted_01_01_07_06 : b4RawGapContribution ![1, 1, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 7, 6] = b4GapPatternWeight 1 7 6 * 0 :=
      b4GapContribution_from_row 1 1 7 6 0 row_01_01_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_06

theorem row_01_01_07_07 : b4RowContribution (![1, 2, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 9, 16] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 9 + 16 = 28
    decide
  have hzsq : (∑ i, (((![1, 2, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 9^2 + 16^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_07_07

theorem weighted_01_01_07_07 : b4RawGapContribution ![1, 1, 7, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 7, 7] = b4GapPatternWeight 1 7 7 * 0 :=
      b4GapContribution_from_row 1 1 7 7 0 row_01_01_07_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_07

theorem row_01_01_07_08 : b4RowContribution (![1, 2, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 9, 17] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 9 + 17 = 29
    decide
  have hzsq : (∑ i, (((![1, 2, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 375 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 9^2 + 17^2 = 375
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_07_08

theorem weighted_01_01_07_08 : b4RawGapContribution ![1, 1, 7, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 7, 8] = b4GapPatternWeight 1 7 8 * 0 :=
      b4GapContribution_from_row 1 1 7 8 0 row_01_01_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_08

theorem row_01_01_07_09 : b4RowContribution (![1, 2, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 9, 18] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 9 + 18 = 30
    decide
  have hzsq : (∑ i, (((![1, 2, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 410 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 9^2 + 18^2 = 410
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_07_09

theorem weighted_01_01_07_09 : b4RawGapContribution ![1, 1, 7, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 7, 9] = b4GapPatternWeight 1 7 9 * 0 :=
      b4GapContribution_from_row 1 1 7 9 0 row_01_01_07_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_09

theorem row_01_01_07_10 : b4RowContribution (![1, 2, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 9, 19] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 9 + 19 = 31
    decide
  have hzsq : (∑ i, (((![1, 2, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 447 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 9^2 + 19^2 = 447
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_07_10

theorem weighted_01_01_07_10 : b4RawGapContribution ![1, 1, 7, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 7, 10] = b4GapPatternWeight 1 7 10 * 0 :=
      b4GapContribution_from_row 1 1 7 10 0 row_01_01_07_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_10

theorem row_01_01_07_11 : b4RowContribution (![1, 2, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 9, 20] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 9 + 20 = 32
    decide
  have hzsq : (∑ i, (((![1, 2, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 486 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 9^2 + 20^2 = 486
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_07_11

theorem weighted_01_01_07_11 : b4RawGapContribution ![1, 1, 7, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 7, 11] = b4GapPatternWeight 1 7 11 * 0 :=
      b4GapContribution_from_row 1 1 7 11 0 row_01_01_07_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_11

theorem row_01_01_07_12 : b4RowContribution (![1, 2, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 9, 21] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 9 + 21 = 33
    decide
  have hzsq : (∑ i, (((![1, 2, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 527 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 9^2 + 21^2 = 527
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_07_12

theorem weighted_01_01_07_12 : b4RawGapContribution ![1, 1, 7, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 7, 12] = b4GapPatternWeight 1 7 12 * 0 :=
      b4GapContribution_from_row 1 1 7 12 0 row_01_01_07_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_12

def layers_01_01_07_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 6, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 27, 33, 39, 45, 51, 56, 59, 60, 60, 60, 60, 60, 60, 60]]
#print axioms Paper7MomentGapNumeric.layers_01_01_07_13

theorem cells_01_01_07_13 : QTableValid (![1, 2, 9, 22] : Fin 4 → ℕ) layers_01_01_07_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_07_13

theorem valid_01_01_07_13 :
    SparseRowValid (![1, 2, 9, 22] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_01_01_07_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 9, 22] : Fin 4 → ℕ) i) = 34 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 9 + 22 = 34
      decide
    have hzsq : (∑ i, (((![1, 2, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 570 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 9^2 + 22^2 = 570
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_07_13
#print axioms Paper7MomentGapNumeric.valid_01_01_07_13

def qvalues_01_01_07_13 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_07_13

theorem row_01_01_07_13 : b4RowContribution (![1, 2, 9, 22] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![1, 2, 9, 22] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_01_01_07_13) :=
      sparseRow_sound (![1, 2, 9, 22] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_01_01_07_13) valid_01_01_07_13
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_07_13 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_01_07_13

theorem weighted_01_01_07_13 : b4RawGapContribution ![1, 1, 7, 13] = 24 := by
  calc
    b4RawGapContribution ![1, 1, 7, 13] = b4GapPatternWeight 1 7 13 * 1 :=
      b4GapContribution_from_row 1 1 7 13 1 row_01_01_07_13
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_13

theorem row_01_01_07_14 : b4RowContribution (![1, 2, 9, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 9, 23] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 9 + 23 = 35
    decide
  have hzsq : (∑ i, (((![1, 2, 9, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 615 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 9^2 + 23^2 = 615
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_07_14

theorem weighted_01_01_07_14 : b4RawGapContribution ![1, 1, 7, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 7, 14] = b4GapPatternWeight 1 7 14 * 0 :=
      b4GapContribution_from_row 1 1 7 14 0 row_01_01_07_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_14

theorem row_01_01_07_15 : b4RowContribution (![1, 2, 9, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 9, 24] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 9 + 24 = 36
    decide
  have hzsq : (∑ i, (((![1, 2, 9, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 662 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 9^2 + 24^2 = 662
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_07_15

theorem weighted_01_01_07_15 : b4RawGapContribution ![1, 1, 7, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 7, 15] = b4GapPatternWeight 1 7 15 * 0 :=
      b4GapContribution_from_row 1 1 7 15 0 row_01_01_07_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_15

theorem row_01_01_07_16 : b4RowContribution (![1, 2, 9, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 9, 25] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 9 + 25 = 37
    decide
  have hzsq : (∑ i, (((![1, 2, 9, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 711 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 9^2 + 25^2 = 711
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_07_16

theorem weighted_01_01_07_16 : b4RawGapContribution ![1, 1, 7, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 7, 16] = b4GapPatternWeight 1 7 16 * 0 :=
      b4GapContribution_from_row 1 1 7 16 0 row_01_01_07_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_07_16

def dvalues_01_01_07 : Fin 17 → ℕ := ![0, 24, 0, 2064, 0, 792, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_01_07

theorem dblock_01_01_07 : b4GapPatternDBlock 1 1 7 = 2904 := by
  calc
    b4GapPatternDBlock 1 1 7 = ∑ d : Fin 17, dvalues_01_01_07 d := by
      apply b4GapDBlock_of_rows 1 1 7 dvalues_01_01_07
      intro d
      fin_cases d
      · exact weighted_01_01_07_00
      · exact weighted_01_01_07_01
      · exact weighted_01_01_07_02
      · exact weighted_01_01_07_03
      · exact weighted_01_01_07_04
      · exact weighted_01_01_07_05
      · exact weighted_01_01_07_06
      · exact weighted_01_01_07_07
      · exact weighted_01_01_07_08
      · exact weighted_01_01_07_09
      · exact weighted_01_01_07_10
      · exact weighted_01_01_07_11
      · exact weighted_01_01_07_12
      · exact weighted_01_01_07_13
      · exact weighted_01_01_07_14
      · exact weighted_01_01_07_15
      · exact weighted_01_01_07_16
    _ = 2904 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_01_07

end Paper7MomentGapNumeric
