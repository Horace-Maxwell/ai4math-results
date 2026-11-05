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

def layers_00_04_06_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 35, 40, 45, 48, 49, 48, 45, 40, 35, 30, 25]]
#print axioms Paper7MomentGapNumeric.layers_00_04_06_00

theorem cells_00_04_06_00 : QTableValid (![0, 4, 10, 10] : Fin 4 → ℕ) layers_00_04_06_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_06_00

theorem valid_00_04_06_00 :
    SparseRowValid (![0, 4, 10, 10] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_04_06_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 10, 10] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 10 + 10 = 24
      decide
    have hzsq : (∑ i, (((![0, 4, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 216 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 10^2 + 10^2 = 216
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_06_00
#print axioms Paper7MomentGapNumeric.valid_00_04_06_00

def qvalues_00_04_06_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_06_00

theorem row_00_04_06_00 : b4RowContribution (![0, 4, 10, 10] : Fin 4 → ℕ) = 49 := by
  calc
    b4RowContribution (![0, 4, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_00_04_06_00) :=
      sparseRow_sound (![0, 4, 10, 10] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_04_06_00) valid_00_04_06_00
    _ = 49 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_06_00 Q := by
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
        _ = 49 := by decide
#print axioms Paper7MomentGapNumeric.row_00_04_06_00

theorem weighted_00_04_06_00 : b4RawGapContribution ![0, 4, 6, 0] = 588 := by
  calc
    b4RawGapContribution ![0, 4, 6, 0] = b4GapPatternWeight 4 6 0 * 49 :=
      b4GapContribution_from_row 0 4 6 0 49 row_00_04_06_00
    _ = 588 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_06_00

def layers_00_04_06_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 35, 40, 45, 49, 51, 51, 49, 45, 40, 35, 30]]
#print axioms Paper7MomentGapNumeric.layers_00_04_06_01

theorem cells_00_04_06_01 : QTableValid (![0, 4, 10, 11] : Fin 4 → ℕ) layers_00_04_06_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_06_01

theorem valid_00_04_06_01 :
    SparseRowValid (![0, 4, 10, 11] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_00_04_06_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 10, 11] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 10 + 11 = 25
      decide
    have hzsq : (∑ i, (((![0, 4, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 237 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 10^2 + 11^2 = 237
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_06_01
#print axioms Paper7MomentGapNumeric.valid_00_04_06_01

def qvalues_00_04_06_01 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_06_01

theorem row_00_04_06_01 : b4RowContribution (![0, 4, 10, 11] : Fin 4 → ℕ) = 26 := by
  calc
    b4RowContribution (![0, 4, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_00_04_06_01) :=
      sparseRow_sound (![0, 4, 10, 11] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_00_04_06_01) valid_00_04_06_01
    _ = 26 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_06_01 Q := by
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
        _ = 26 := by decide
#print axioms Paper7MomentGapNumeric.row_00_04_06_01

theorem weighted_00_04_06_01 : b4RawGapContribution ![0, 4, 6, 1] = 624 := by
  calc
    b4RawGapContribution ![0, 4, 6, 1] = b4GapPatternWeight 4 6 1 * 26 :=
      b4GapContribution_from_row 0 4 6 1 26 row_00_04_06_01
    _ = 624 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_06_01

theorem row_00_04_06_02 : b4RowContribution (![0, 4, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 10, 12] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 10 + 12 = 26
    decide
  have hzsq : (∑ i, (((![0, 4, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 260 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 10^2 + 12^2 = 260
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_06_02

theorem weighted_00_04_06_02 : b4RawGapContribution ![0, 4, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 6, 2] = b4GapPatternWeight 4 6 2 * 0 :=
      b4GapContribution_from_row 0 4 6 2 0 row_00_04_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_06_02

def layers_00_04_06_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 35, 40, 45, 49, 52, 54, 54, 52, 49, 45, 40]]
#print axioms Paper7MomentGapNumeric.layers_00_04_06_03

theorem cells_00_04_06_03 : QTableValid (![0, 4, 10, 13] : Fin 4 → ℕ) layers_00_04_06_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_06_03

theorem valid_00_04_06_03 :
    SparseRowValid (![0, 4, 10, 13] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_04_06_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 10, 13] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 10 + 13 = 27
      decide
    have hzsq : (∑ i, (((![0, 4, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 285 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 10^2 + 13^2 = 285
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_06_03
#print axioms Paper7MomentGapNumeric.valid_00_04_06_03

def qvalues_00_04_06_03 : Fin 19 → ℕ := ![0, 0, 0, 10, 0, 0, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_06_03

theorem row_00_04_06_03 : b4RowContribution (![0, 4, 10, 13] : Fin 4 → ℕ) = 50 := by
  calc
    b4RowContribution (![0, 4, 10, 13] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_04_06_03) :=
      sparseRow_sound (![0, 4, 10, 13] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_04_06_03) valid_00_04_06_03
    _ = 50 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_06_03 Q := by
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
        _ = 50 := by decide
#print axioms Paper7MomentGapNumeric.row_00_04_06_03

theorem weighted_00_04_06_03 : b4RawGapContribution ![0, 4, 6, 3] = 1200 := by
  calc
    b4RawGapContribution ![0, 4, 6, 3] = b4GapPatternWeight 4 6 3 * 50 :=
      b4GapContribution_from_row 0 4 6 3 50 row_00_04_06_03
    _ = 1200 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_06_03

theorem row_00_04_06_04 : b4RowContribution (![0, 4, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 10, 14] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 10 + 14 = 28
    decide
  have hzsq : (∑ i, (((![0, 4, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 312 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 10^2 + 14^2 = 312
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_06_04

theorem weighted_00_04_06_04 : b4RawGapContribution ![0, 4, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 6, 4] = b4GapPatternWeight 4 6 4 * 0 :=
      b4GapContribution_from_row 0 4 6 4 0 row_00_04_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_06_04

theorem row_00_04_06_05 : b4RowContribution (![0, 4, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 10, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 10 + 15 = 29
    decide
  have hzsq : (∑ i, (((![0, 4, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 341 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 10^2 + 15^2 = 341
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_06_05

theorem weighted_00_04_06_05 : b4RawGapContribution ![0, 4, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 6, 5] = b4GapPatternWeight 4 6 5 * 0 :=
      b4GapContribution_from_row 0 4 6 5 0 row_00_04_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_06_05

theorem row_00_04_06_06 : b4RowContribution (![0, 4, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 10, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 10 + 16 = 30
    decide
  have hzsq : (∑ i, (((![0, 4, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 372 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 10^2 + 16^2 = 372
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_06_06

theorem weighted_00_04_06_06 : b4RawGapContribution ![0, 4, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 6, 6] = b4GapPatternWeight 4 6 6 * 0 :=
      b4GapContribution_from_row 0 4 6 6 0 row_00_04_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_06_06

theorem row_00_04_06_07 : b4RowContribution (![0, 4, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 10, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 10 + 17 = 31
    decide
  have hzsq : (∑ i, (((![0, 4, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 405 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 10^2 + 17^2 = 405
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_06_07

theorem weighted_00_04_06_07 : b4RawGapContribution ![0, 4, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 6, 7] = b4GapPatternWeight 4 6 7 * 0 :=
      b4GapContribution_from_row 0 4 6 7 0 row_00_04_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_06_07

theorem row_00_04_06_08 : b4RowContribution (![0, 4, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 10, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 10 + 18 = 32
    decide
  have hzsq : (∑ i, (((![0, 4, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 440 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 10^2 + 18^2 = 440
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_06_08

theorem weighted_00_04_06_08 : b4RawGapContribution ![0, 4, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 6, 8] = b4GapPatternWeight 4 6 8 * 0 :=
      b4GapContribution_from_row 0 4 6 8 0 row_00_04_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_06_08

theorem row_00_04_06_09 : b4RowContribution (![0, 4, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 10, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 10 + 19 = 33
    decide
  have hzsq : (∑ i, (((![0, 4, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 477 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 10^2 + 19^2 = 477
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_06_09

theorem weighted_00_04_06_09 : b4RawGapContribution ![0, 4, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 6, 9] = b4GapPatternWeight 4 6 9 * 0 :=
      b4GapContribution_from_row 0 4 6 9 0 row_00_04_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_06_09

theorem row_00_04_06_10 : b4RowContribution (![0, 4, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 10, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 10 + 20 = 34
    decide
  have hzsq : (∑ i, (((![0, 4, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 516 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 10^2 + 20^2 = 516
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_06_10

theorem weighted_00_04_06_10 : b4RawGapContribution ![0, 4, 6, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 6, 10] = b4GapPatternWeight 4 6 10 * 0 :=
      b4GapContribution_from_row 0 4 6 10 0 row_00_04_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_06_10

theorem row_00_04_06_11 : b4RowContribution (![0, 4, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 10, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 10 + 21 = 35
    decide
  have hzsq : (∑ i, (((![0, 4, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 557 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 10^2 + 21^2 = 557
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_06_11

theorem weighted_00_04_06_11 : b4RawGapContribution ![0, 4, 6, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 6, 11] = b4GapPatternWeight 4 6 11 * 0 :=
      b4GapContribution_from_row 0 4 6 11 0 row_00_04_06_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_06_11

theorem row_00_04_06_12 : b4RowContribution (![0, 4, 10, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 10, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 10 + 22 = 36
    decide
  have hzsq : (∑ i, (((![0, 4, 10, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 600 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 10^2 + 22^2 = 600
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_06_12

theorem weighted_00_04_06_12 : b4RawGapContribution ![0, 4, 6, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 6, 12] = b4GapPatternWeight 4 6 12 * 0 :=
      b4GapContribution_from_row 0 4 6 12 0 row_00_04_06_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_06_12

theorem row_00_04_06_13 : b4RowContribution (![0, 4, 10, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 10, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 10 + 23 = 37
    decide
  have hzsq : (∑ i, (((![0, 4, 10, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 645 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 10^2 + 23^2 = 645
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_06_13

theorem weighted_00_04_06_13 : b4RawGapContribution ![0, 4, 6, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 6, 13] = b4GapPatternWeight 4 6 13 * 0 :=
      b4GapContribution_from_row 0 4 6 13 0 row_00_04_06_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_06_13

def dvalues_00_04_06 : Fin 14 → ℕ := ![588, 624, 0, 1200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_04_06

theorem dblock_00_04_06 : b4GapPatternDBlock 0 4 6 = 2412 := by
  calc
    b4GapPatternDBlock 0 4 6 = ∑ d : Fin 14, dvalues_00_04_06 d := by
      apply b4GapDBlock_of_rows 0 4 6 dvalues_00_04_06
      intro d
      fin_cases d
      · exact weighted_00_04_06_00
      · exact weighted_00_04_06_01
      · exact weighted_00_04_06_02
      · exact weighted_00_04_06_03
      · exact weighted_00_04_06_04
      · exact weighted_00_04_06_05
      · exact weighted_00_04_06_06
      · exact weighted_00_04_06_07
      · exact weighted_00_04_06_08
      · exact weighted_00_04_06_09
      · exact weighted_00_04_06_10
      · exact weighted_00_04_06_11
      · exact weighted_00_04_06_12
      · exact weighted_00_04_06_13
    _ = 2412 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_04_06

end Paper7MomentGapNumeric
