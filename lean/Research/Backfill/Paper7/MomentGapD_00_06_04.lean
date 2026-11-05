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

def layers_00_06_04_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 7, 7, 7, 6, 5, 4, 3, 2, 1, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 35, 42, 49, 56, 61, 64, 65, 64, 61, 56, 49, 42]]
#print axioms Paper7MomentGapNumeric.layers_00_06_04_00

theorem cells_00_06_04_00 : QTableValid (![0, 6, 10, 10] : Fin 4 → ℕ) layers_00_06_04_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_06_04_00

theorem valid_00_06_04_00 :
    SparseRowValid (![0, 6, 10, 10] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_06_04_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 6, 10, 10] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 0 + 6 + 10 + 10 = 26
      decide
    have hzsq : (∑ i, (((![0, 6, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 236 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 6^2 + 10^2 + 10^2 = 236
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_06_04_00
#print axioms Paper7MomentGapNumeric.valid_00_06_04_00

def qvalues_00_06_04_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_06_04_00

theorem row_00_06_04_00 : b4RowContribution (![0, 6, 10, 10] : Fin 4 → ℕ) = 21 := by
  calc
    b4RowContribution (![0, 6, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_00_06_04_00) :=
      sparseRow_sound (![0, 6, 10, 10] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_06_04_00) valid_00_06_04_00
    _ = 21 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_06_04_00 Q := by
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
        _ = 21 := by decide
#print axioms Paper7MomentGapNumeric.row_00_06_04_00

theorem weighted_00_06_04_00 : b4RawGapContribution ![0, 6, 4, 0] = 252 := by
  calc
    b4RawGapContribution ![0, 6, 4, 0] = b4GapPatternWeight 6 4 0 * 21 :=
      b4GapContribution_from_row 0 6 4 0 21 row_00_06_04_00
    _ = 252 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_04_00

theorem row_00_06_04_01 : b4RowContribution (![0, 6, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 10, 11] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 10 + 11 = 27
    decide
  have hzsq : (∑ i, (((![0, 6, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 257 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 10^2 + 11^2 = 257
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_04_01

theorem weighted_00_06_04_01 : b4RawGapContribution ![0, 6, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 4, 1] = b4GapPatternWeight 6 4 1 * 0 :=
      b4GapContribution_from_row 0 6 4 1 0 row_00_06_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_04_01

def layers_00_06_04_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 7, 7, 7, 6, 5, 4, 3, 2, 1, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 35, 42, 49, 56, 62, 67, 70, 71, 70, 67, 62, 56]]
#print axioms Paper7MomentGapNumeric.layers_00_06_04_02

theorem cells_00_06_04_02 : QTableValid (![0, 6, 10, 12] : Fin 4 → ℕ) layers_00_06_04_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_06_04_02

theorem valid_00_06_04_02 :
    SparseRowValid (![0, 6, 10, 12] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_00_06_04_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 6, 10, 12] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 0 + 6 + 10 + 12 = 28
      decide
    have hzsq : (∑ i, (((![0, 6, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 280 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 6^2 + 10^2 + 12^2 = 280
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_06_04_02
#print axioms Paper7MomentGapNumeric.valid_00_06_04_02

def qvalues_00_06_04_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_06_04_02

theorem row_00_06_04_02 : b4RowContribution (![0, 6, 10, 12] : Fin 4 → ℕ) = 15 := by
  calc
    b4RowContribution (![0, 6, 10, 12] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_00_06_04_02) :=
      sparseRow_sound (![0, 6, 10, 12] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_00_06_04_02) valid_00_06_04_02
    _ = 15 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_06_04_02 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 15 := by decide
#print axioms Paper7MomentGapNumeric.row_00_06_04_02

theorem weighted_00_06_04_02 : b4RawGapContribution ![0, 6, 4, 2] = 360 := by
  calc
    b4RawGapContribution ![0, 6, 4, 2] = b4GapPatternWeight 6 4 2 * 15 :=
      b4GapContribution_from_row 0 6 4 2 15 row_00_06_04_02
    _ = 360 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_04_02

theorem row_00_06_04_03 : b4RowContribution (![0, 6, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 10, 13] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 10 + 13 = 29
    decide
  have hzsq : (∑ i, (((![0, 6, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 305 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 10^2 + 13^2 = 305
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_04_03

theorem weighted_00_06_04_03 : b4RawGapContribution ![0, 6, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 4, 3] = b4GapPatternWeight 6 4 3 * 0 :=
      b4GapContribution_from_row 0 6 4 3 0 row_00_06_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_04_03

theorem row_00_06_04_04 : b4RowContribution (![0, 6, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 10, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 10 + 14 = 30
    decide
  have hzsq : (∑ i, (((![0, 6, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 332 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 10^2 + 14^2 = 332
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_04_04

theorem weighted_00_06_04_04 : b4RawGapContribution ![0, 6, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 4, 4] = b4GapPatternWeight 6 4 4 * 0 :=
      b4GapContribution_from_row 0 6 4 4 0 row_00_06_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_04_04

theorem row_00_06_04_05 : b4RowContribution (![0, 6, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 10, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 10 + 15 = 31
    decide
  have hzsq : (∑ i, (((![0, 6, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 361 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 10^2 + 15^2 = 361
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_04_05

theorem weighted_00_06_04_05 : b4RawGapContribution ![0, 6, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 4, 5] = b4GapPatternWeight 6 4 5 * 0 :=
      b4GapContribution_from_row 0 6 4 5 0 row_00_06_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_04_05

theorem row_00_06_04_06 : b4RowContribution (![0, 6, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 10, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 10 + 16 = 32
    decide
  have hzsq : (∑ i, (((![0, 6, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 392 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 10^2 + 16^2 = 392
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_04_06

theorem weighted_00_06_04_06 : b4RawGapContribution ![0, 6, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 4, 6] = b4GapPatternWeight 6 4 6 * 0 :=
      b4GapContribution_from_row 0 6 4 6 0 row_00_06_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_04_06

theorem row_00_06_04_07 : b4RowContribution (![0, 6, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 10, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 10 + 17 = 33
    decide
  have hzsq : (∑ i, (((![0, 6, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 425 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 10^2 + 17^2 = 425
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_04_07

theorem weighted_00_06_04_07 : b4RawGapContribution ![0, 6, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 4, 7] = b4GapPatternWeight 6 4 7 * 0 :=
      b4GapContribution_from_row 0 6 4 7 0 row_00_06_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_04_07

theorem row_00_06_04_08 : b4RowContribution (![0, 6, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 10, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 10 + 18 = 34
    decide
  have hzsq : (∑ i, (((![0, 6, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 460 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 10^2 + 18^2 = 460
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_04_08

theorem weighted_00_06_04_08 : b4RawGapContribution ![0, 6, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 4, 8] = b4GapPatternWeight 6 4 8 * 0 :=
      b4GapContribution_from_row 0 6 4 8 0 row_00_06_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_04_08

theorem row_00_06_04_09 : b4RowContribution (![0, 6, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 10, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 10 + 19 = 35
    decide
  have hzsq : (∑ i, (((![0, 6, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 497 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 10^2 + 19^2 = 497
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_04_09

theorem weighted_00_06_04_09 : b4RawGapContribution ![0, 6, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 4, 9] = b4GapPatternWeight 6 4 9 * 0 :=
      b4GapContribution_from_row 0 6 4 9 0 row_00_06_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_04_09

theorem row_00_06_04_10 : b4RowContribution (![0, 6, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 10, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 10 + 20 = 36
    decide
  have hzsq : (∑ i, (((![0, 6, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 536 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 10^2 + 20^2 = 536
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_04_10

theorem weighted_00_06_04_10 : b4RawGapContribution ![0, 6, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 4, 10] = b4GapPatternWeight 6 4 10 * 0 :=
      b4GapContribution_from_row 0 6 4 10 0 row_00_06_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_04_10

theorem row_00_06_04_11 : b4RowContribution (![0, 6, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 10, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 10 + 21 = 37
    decide
  have hzsq : (∑ i, (((![0, 6, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 577 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 10^2 + 21^2 = 577
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_04_11

theorem weighted_00_06_04_11 : b4RawGapContribution ![0, 6, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 4, 11] = b4GapPatternWeight 6 4 11 * 0 :=
      b4GapContribution_from_row 0 6 4 11 0 row_00_06_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_04_11

def dvalues_00_06_04 : Fin 12 → ℕ := ![252, 0, 360, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_06_04

theorem dblock_00_06_04 : b4GapPatternDBlock 0 6 4 = 612 := by
  calc
    b4GapPatternDBlock 0 6 4 = ∑ d : Fin 12, dvalues_00_06_04 d := by
      apply b4GapDBlock_of_rows 0 6 4 dvalues_00_06_04
      intro d
      fin_cases d
      · exact weighted_00_06_04_00
      · exact weighted_00_06_04_01
      · exact weighted_00_06_04_02
      · exact weighted_00_06_04_03
      · exact weighted_00_06_04_04
      · exact weighted_00_06_04_05
      · exact weighted_00_06_04_06
      · exact weighted_00_06_04_07
      · exact weighted_00_06_04_08
      · exact weighted_00_06_04_09
      · exact weighted_00_06_04_10
      · exact weighted_00_06_04_11
    _ = 612 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_06_04

end Paper7MomentGapNumeric
