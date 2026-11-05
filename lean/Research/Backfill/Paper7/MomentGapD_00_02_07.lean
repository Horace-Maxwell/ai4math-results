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

def layers_00_02_07_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 27, 28, 27, 24, 21, 18, 15, 12, 9, 6]]
#print axioms Paper7MomentGapNumeric.layers_00_02_07_00

theorem cells_00_02_07_00 : QTableValid (![0, 2, 9, 9] : Fin 4 → ℕ) layers_00_02_07_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_07_00

theorem valid_00_02_07_00 :
    SparseRowValid (![0, 2, 9, 9] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_00_02_07_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 9, 9] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 9 + 9 = 20
      decide
    have hzsq : (∑ i, (((![0, 2, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 166 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 9^2 + 9^2 = 166
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_07_00
#print axioms Paper7MomentGapNumeric.valid_00_02_07_00

def qvalues_00_02_07_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_07_00

theorem row_00_02_07_00 : b4RowContribution (![0, 2, 9, 9] : Fin 4 → ℕ) = 21 := by
  calc
    b4RowContribution (![0, 2, 9, 9] : Fin 4 → ℕ) =
        sparseRowValue ({13} : Finset (Fin 19)) (fun _ => layers_00_02_07_00) :=
      sparseRow_sound (![0, 2, 9, 9] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_00_02_07_00) valid_00_02_07_00
    _ = 21 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_07_00 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 21 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_07_00

theorem weighted_00_02_07_00 : b4RawGapContribution ![0, 2, 7, 0] = 252 := by
  calc
    b4RawGapContribution ![0, 2, 7, 0] = b4GapPatternWeight 2 7 0 * 21 :=
      b4GapContribution_from_row 0 2 7 0 21 row_00_02_07_00
    _ = 252 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_00

theorem row_00_02_07_01 : b4RowContribution (![0, 2, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 9, 10] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 9 + 10 = 21
    decide
  have hzsq : (∑ i, (((![0, 2, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 185 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 9^2 + 10^2 = 185
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_07_01

theorem weighted_00_02_07_01 : b4RawGapContribution ![0, 2, 7, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 7, 1] = b4GapPatternWeight 2 7 1 * 0 :=
      b4GapContribution_from_row 0 2 7 1 0 row_00_02_07_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_01

theorem row_00_02_07_02 : b4RowContribution (![0, 2, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 9, 11] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 9 + 11 = 22
    decide
  have hzsq : (∑ i, (((![0, 2, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 206 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 9^2 + 11^2 = 206
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_07_02

theorem weighted_00_02_07_02 : b4RawGapContribution ![0, 2, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 7, 2] = b4GapPatternWeight 2 7 2 * 0 :=
      b4GapContribution_from_row 0 2 7 2 0 row_00_02_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_02

def layers_00_02_07_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 27, 29, 30, 30, 29, 27, 24, 21, 18, 15]]
#print axioms Paper7MomentGapNumeric.layers_00_02_07_03

theorem cells_00_02_07_03 : QTableValid (![0, 2, 9, 12] : Fin 4 → ℕ) layers_00_02_07_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_07_03

theorem valid_00_02_07_03 :
    SparseRowValid (![0, 2, 9, 12] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_00_02_07_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 9, 12] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 9 + 12 = 23
      decide
    have hzsq : (∑ i, (((![0, 2, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 229 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 9^2 + 12^2 = 229
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_07_03
#print axioms Paper7MomentGapNumeric.valid_00_02_07_03

def qvalues_00_02_07_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 29, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_07_03

theorem row_00_02_07_03 : b4RowContribution (![0, 2, 9, 12] : Fin 4 → ℕ) = 50 := by
  calc
    b4RowContribution (![0, 2, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({7, 13} : Finset (Fin 19)) (fun _ => layers_00_02_07_03) :=
      sparseRow_sound (![0, 2, 9, 12] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_00_02_07_03) valid_00_02_07_03
    _ = 50 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_07_03 Q := by
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
        _ = 50 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_07_03

theorem weighted_00_02_07_03 : b4RawGapContribution ![0, 2, 7, 3] = 1200 := by
  calc
    b4RawGapContribution ![0, 2, 7, 3] = b4GapPatternWeight 2 7 3 * 50 :=
      b4GapContribution_from_row 0 2 7 3 50 row_00_02_07_03
    _ = 1200 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_03

theorem row_00_02_07_04 : b4RowContribution (![0, 2, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 9, 13] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 9 + 13 = 24
    decide
  have hzsq : (∑ i, (((![0, 2, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 254 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 9^2 + 13^2 = 254
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_07_04

theorem weighted_00_02_07_04 : b4RawGapContribution ![0, 2, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 7, 4] = b4GapPatternWeight 2 7 4 * 0 :=
      b4GapContribution_from_row 0 2 7 4 0 row_00_02_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_04

def layers_00_02_07_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 27, 29, 30, 30, 30, 30, 29, 27, 24, 21]]
#print axioms Paper7MomentGapNumeric.layers_00_02_07_05

theorem cells_00_02_07_05 : QTableValid (![0, 2, 9, 14] : Fin 4 → ℕ) layers_00_02_07_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_07_05

theorem valid_00_02_07_05 :
    SparseRowValid (![0, 2, 9, 14] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_02_07_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 9, 14] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 9 + 14 = 25
      decide
    have hzsq : (∑ i, (((![0, 2, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 281 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 9^2 + 14^2 = 281
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_07_05
#print axioms Paper7MomentGapNumeric.valid_00_02_07_05

def qvalues_00_02_07_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_07_05

theorem row_00_02_07_05 : b4RowContribution (![0, 2, 9, 14] : Fin 4 → ℕ) = 24 := by
  calc
    b4RowContribution (![0, 2, 9, 14] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_00_02_07_05) :=
      sparseRow_sound (![0, 2, 9, 14] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_00_02_07_05) valid_00_02_07_05
    _ = 24 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_07_05 Q := by
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
        _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_07_05

theorem weighted_00_02_07_05 : b4RawGapContribution ![0, 2, 7, 5] = 576 := by
  calc
    b4RawGapContribution ![0, 2, 7, 5] = b4GapPatternWeight 2 7 5 * 24 :=
      b4GapContribution_from_row 0 2 7 5 24 row_00_02_07_05
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_05

theorem row_00_02_07_06 : b4RowContribution (![0, 2, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 9, 15] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 9 + 15 = 26
    decide
  have hzsq : (∑ i, (((![0, 2, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 310 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 9^2 + 15^2 = 310
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_07_06

theorem weighted_00_02_07_06 : b4RawGapContribution ![0, 2, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 7, 6] = b4GapPatternWeight 2 7 6 * 0 :=
      b4GapContribution_from_row 0 2 7 6 0 row_00_02_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_06

theorem row_00_02_07_07 : b4RowContribution (![0, 2, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 9, 16] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 9 + 16 = 27
    decide
  have hzsq : (∑ i, (((![0, 2, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 341 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 9^2 + 16^2 = 341
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_07_07

theorem weighted_00_02_07_07 : b4RawGapContribution ![0, 2, 7, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 7, 7] = b4GapPatternWeight 2 7 7 * 0 :=
      b4GapContribution_from_row 0 2 7 7 0 row_00_02_07_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_07

theorem row_00_02_07_08 : b4RowContribution (![0, 2, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 9, 17] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 9 + 17 = 28
    decide
  have hzsq : (∑ i, (((![0, 2, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 374 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 9^2 + 17^2 = 374
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_07_08

theorem weighted_00_02_07_08 : b4RawGapContribution ![0, 2, 7, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 7, 8] = b4GapPatternWeight 2 7 8 * 0 :=
      b4GapContribution_from_row 0 2 7 8 0 row_00_02_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_08

theorem row_00_02_07_09 : b4RowContribution (![0, 2, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 9, 18] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 9 + 18 = 29
    decide
  have hzsq : (∑ i, (((![0, 2, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 409 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 9^2 + 18^2 = 409
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_07_09

theorem weighted_00_02_07_09 : b4RawGapContribution ![0, 2, 7, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 7, 9] = b4GapPatternWeight 2 7 9 * 0 :=
      b4GapContribution_from_row 0 2 7 9 0 row_00_02_07_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_09

theorem row_00_02_07_10 : b4RowContribution (![0, 2, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 9, 19] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 9 + 19 = 30
    decide
  have hzsq : (∑ i, (((![0, 2, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 446 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 9^2 + 19^2 = 446
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_07_10

theorem weighted_00_02_07_10 : b4RawGapContribution ![0, 2, 7, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 7, 10] = b4GapPatternWeight 2 7 10 * 0 :=
      b4GapContribution_from_row 0 2 7 10 0 row_00_02_07_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_10

theorem row_00_02_07_11 : b4RowContribution (![0, 2, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 9, 20] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 9 + 20 = 31
    decide
  have hzsq : (∑ i, (((![0, 2, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 485 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 9^2 + 20^2 = 485
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_07_11

theorem weighted_00_02_07_11 : b4RawGapContribution ![0, 2, 7, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 7, 11] = b4GapPatternWeight 2 7 11 * 0 :=
      b4GapContribution_from_row 0 2 7 11 0 row_00_02_07_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_11

theorem row_00_02_07_12 : b4RowContribution (![0, 2, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 9, 21] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 9 + 21 = 32
    decide
  have hzsq : (∑ i, (((![0, 2, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 526 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 9^2 + 21^2 = 526
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_07_12

theorem weighted_00_02_07_12 : b4RawGapContribution ![0, 2, 7, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 7, 12] = b4GapPatternWeight 2 7 12 * 0 :=
      b4GapContribution_from_row 0 2 7 12 0 row_00_02_07_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_12

def layers_00_02_07_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 27, 29, 30, 30, 30, 30, 30, 30, 30, 30]]
#print axioms Paper7MomentGapNumeric.layers_00_02_07_13

theorem cells_00_02_07_13 : QTableValid (![0, 2, 9, 22] : Fin 4 → ℕ) layers_00_02_07_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_02_07_13

theorem valid_00_02_07_13 :
    SparseRowValid (![0, 2, 9, 22] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_00_02_07_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 2, 9, 22] : Fin 4 → ℕ) i) = 33 := by
      rw [Fin.sum_univ_four]
      change 0 + 2 + 9 + 22 = 33
      decide
    have hzsq : (∑ i, (((![0, 2, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 569 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 2^2 + 9^2 + 22^2 = 569
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_02_07_13
#print axioms Paper7MomentGapNumeric.valid_00_02_07_13

def qvalues_00_02_07_13 : Fin 19 → ℕ := ![0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_02_07_13

theorem row_00_02_07_13 : b4RowContribution (![0, 2, 9, 22] : Fin 4 → ℕ) = 6 := by
  calc
    b4RowContribution (![0, 2, 9, 22] : Fin 4 → ℕ) =
        sparseRowValue ({2} : Finset (Fin 19)) (fun _ => layers_00_02_07_13) :=
      sparseRow_sound (![0, 2, 9, 22] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_00_02_07_13) valid_00_02_07_13
    _ = 6 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_02_07_13 Q := by
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
        _ = 6 := by decide
#print axioms Paper7MomentGapNumeric.row_00_02_07_13

theorem weighted_00_02_07_13 : b4RawGapContribution ![0, 2, 7, 13] = 144 := by
  calc
    b4RawGapContribution ![0, 2, 7, 13] = b4GapPatternWeight 2 7 13 * 6 :=
      b4GapContribution_from_row 0 2 7 13 6 row_00_02_07_13
    _ = 144 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_13

theorem row_00_02_07_14 : b4RowContribution (![0, 2, 9, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 9, 23] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 9 + 23 = 34
    decide
  have hzsq : (∑ i, (((![0, 2, 9, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 614 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 9^2 + 23^2 = 614
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_07_14

theorem weighted_00_02_07_14 : b4RawGapContribution ![0, 2, 7, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 7, 14] = b4GapPatternWeight 2 7 14 * 0 :=
      b4GapContribution_from_row 0 2 7 14 0 row_00_02_07_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_14

theorem row_00_02_07_15 : b4RowContribution (![0, 2, 9, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 9, 24] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 9 + 24 = 35
    decide
  have hzsq : (∑ i, (((![0, 2, 9, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 661 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 9^2 + 24^2 = 661
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_07_15

theorem weighted_00_02_07_15 : b4RawGapContribution ![0, 2, 7, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 7, 15] = b4GapPatternWeight 2 7 15 * 0 :=
      b4GapContribution_from_row 0 2 7 15 0 row_00_02_07_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_15

theorem row_00_02_07_16 : b4RowContribution (![0, 2, 9, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 9, 25] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 9 + 25 = 36
    decide
  have hzsq : (∑ i, (((![0, 2, 9, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 710 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 9^2 + 25^2 = 710
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_07_16

theorem weighted_00_02_07_16 : b4RawGapContribution ![0, 2, 7, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 7, 16] = b4GapPatternWeight 2 7 16 * 0 :=
      b4GapContribution_from_row 0 2 7 16 0 row_00_02_07_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_16

theorem row_00_02_07_17 : b4RowContribution (![0, 2, 9, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 2, 9, 26] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 2 + 9 + 26 = 37
    decide
  have hzsq : (∑ i, (((![0, 2, 9, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 761 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 2^2 + 9^2 + 26^2 = 761
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_02_07_17

theorem weighted_00_02_07_17 : b4RawGapContribution ![0, 2, 7, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 2, 7, 17] = b4GapPatternWeight 2 7 17 * 0 :=
      b4GapContribution_from_row 0 2 7 17 0 row_00_02_07_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_02_07_17

def dvalues_00_02_07 : Fin 18 → ℕ := ![252, 0, 0, 1200, 0, 576, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_02_07

theorem dblock_00_02_07 : b4GapPatternDBlock 0 2 7 = 2172 := by
  calc
    b4GapPatternDBlock 0 2 7 = ∑ d : Fin 18, dvalues_00_02_07 d := by
      apply b4GapDBlock_of_rows 0 2 7 dvalues_00_02_07
      intro d
      fin_cases d
      · exact weighted_00_02_07_00
      · exact weighted_00_02_07_01
      · exact weighted_00_02_07_02
      · exact weighted_00_02_07_03
      · exact weighted_00_02_07_04
      · exact weighted_00_02_07_05
      · exact weighted_00_02_07_06
      · exact weighted_00_02_07_07
      · exact weighted_00_02_07_08
      · exact weighted_00_02_07_09
      · exact weighted_00_02_07_10
      · exact weighted_00_02_07_11
      · exact weighted_00_02_07_12
      · exact weighted_00_02_07_13
      · exact weighted_00_02_07_14
      · exact weighted_00_02_07_15
      · exact weighted_00_02_07_16
      · exact weighted_00_02_07_17
    _ = 2172 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_02_07

end Paper7MomentGapNumeric
