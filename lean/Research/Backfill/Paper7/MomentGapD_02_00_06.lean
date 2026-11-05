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

theorem row_02_00_06_00 : b4RowContribution (![2, 2, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 8] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 8 = 20
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 136 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 8^2 = 136
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_00

theorem weighted_02_00_06_00 : b4RawGapContribution ![2, 0, 6, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 0] = b4GapPatternWeight 0 6 0 * 0 :=
      b4GapContribution_from_row 2 0 6 0 0 row_02_00_06_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_00

theorem row_02_00_06_01 : b4RowContribution (![2, 2, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 9] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 9 = 21
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 153 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 9^2 = 153
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_01

theorem weighted_02_00_06_01 : b4RawGapContribution ![2, 0, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 1] = b4GapPatternWeight 0 6 1 * 0 :=
      b4GapContribution_from_row 2 0 6 1 0 row_02_00_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_01

theorem row_02_00_06_02 : b4RowContribution (![2, 2, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 10] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 10 = 22
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 172 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 10^2 = 172
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_02

theorem weighted_02_00_06_02 : b4RawGapContribution ![2, 0, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 2] = b4GapPatternWeight 0 6 2 * 0 :=
      b4GapContribution_from_row 2 0 6 2 0 row_02_00_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_02

theorem row_02_00_06_03 : b4RowContribution (![2, 2, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 11] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 11 = 23
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 193 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 11^2 = 193
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_03

theorem weighted_02_00_06_03 : b4RawGapContribution ![2, 0, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 3] = b4GapPatternWeight 0 6 3 * 0 :=
      b4GapContribution_from_row 2 0 6 3 0 row_02_00_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_03

def layers_02_00_06_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 9, 9, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 36, 45, 54, 63, 71, 77, 80, 81, 80, 77, 71, 63, 54, 45]]
#print axioms Paper7MomentGapNumeric.layers_02_00_06_04

theorem cells_02_00_06_04 : QTableValid (![2, 2, 8, 12] : Fin 4 → ℕ) layers_02_00_06_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_06_04

theorem valid_02_00_06_04 :
    SparseRowValid (![2, 2, 8, 12] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_02_00_06_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 8, 12] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 8 + 12 = 24
      decide
    have hzsq : (∑ i, (((![2, 2, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 216 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 8^2 + 12^2 = 216
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_06_04
#print axioms Paper7MomentGapNumeric.valid_02_00_06_04

def qvalues_02_00_06_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_06_04

theorem row_02_00_06_04 : b4RowContribution (![2, 2, 8, 12] : Fin 4 → ℕ) = 81 := by
  calc
    b4RowContribution (![2, 2, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_02_00_06_04) :=
      sparseRow_sound (![2, 2, 8, 12] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_02_00_06_04) valid_02_00_06_04
    _ = 81 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_06_04 Q := by
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
        _ = 81 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_06_04

theorem weighted_02_00_06_04 : b4RawGapContribution ![2, 0, 6, 4] = 972 := by
  calc
    b4RawGapContribution ![2, 0, 6, 4] = b4GapPatternWeight 0 6 4 * 81 :=
      b4GapContribution_from_row 2 0 6 4 81 row_02_00_06_04
    _ = 972 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_04

def layers_02_00_06_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 9, 9, 9, 8, 6, 3, 1, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 36, 45, 54, 63, 71, 77, 80, 81, 81, 80, 77, 71, 63, 54]]
#print axioms Paper7MomentGapNumeric.layers_02_00_06_05

theorem cells_02_00_06_05 : QTableValid (![2, 2, 8, 13] : Fin 4 → ℕ) layers_02_00_06_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_06_05

theorem valid_02_00_06_05 :
    SparseRowValid (![2, 2, 8, 13] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_00_06_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 8, 13] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 8 + 13 = 25
      decide
    have hzsq : (∑ i, (((![2, 2, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 241 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 8^2 + 13^2 = 241
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_06_05
#print axioms Paper7MomentGapNumeric.valid_02_00_06_05

def qvalues_02_00_06_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_06_05

theorem row_02_00_06_05 : b4RowContribution (![2, 2, 8, 13] : Fin 4 → ℕ) = 27 := by
  calc
    b4RowContribution (![2, 2, 8, 13] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_02_00_06_05) :=
      sparseRow_sound (![2, 2, 8, 13] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_00_06_05) valid_02_00_06_05
    _ = 27 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_06_05 Q := by
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
        _ = 27 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_06_05

theorem weighted_02_00_06_05 : b4RawGapContribution ![2, 0, 6, 5] = 324 := by
  calc
    b4RawGapContribution ![2, 0, 6, 5] = b4GapPatternWeight 0 6 5 * 27 :=
      b4GapContribution_from_row 2 0 6 5 27 row_02_00_06_05
    _ = 324 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_05

theorem row_02_00_06_06 : b4RowContribution (![2, 2, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 14] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 14 = 26
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 268 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 14^2 = 268
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_06

theorem weighted_02_00_06_06 : b4RawGapContribution ![2, 0, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 6] = b4GapPatternWeight 0 6 6 * 0 :=
      b4GapContribution_from_row 2 0 6 6 0 row_02_00_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_06

theorem row_02_00_06_07 : b4RowContribution (![2, 2, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 15] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 15 = 27
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 297 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 15^2 = 297
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_07

theorem weighted_02_00_06_07 : b4RawGapContribution ![2, 0, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 7] = b4GapPatternWeight 0 6 7 * 0 :=
      b4GapContribution_from_row 2 0 6 7 0 row_02_00_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_07

theorem row_02_00_06_08 : b4RowContribution (![2, 2, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 16] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 16 = 28
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 328 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 16^2 = 328
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_08

theorem weighted_02_00_06_08 : b4RawGapContribution ![2, 0, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 8] = b4GapPatternWeight 0 6 8 * 0 :=
      b4GapContribution_from_row 2 0 6 8 0 row_02_00_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_08

theorem row_02_00_06_09 : b4RowContribution (![2, 2, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 17] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 17 = 29
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 361 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 17^2 = 361
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_09

theorem weighted_02_00_06_09 : b4RawGapContribution ![2, 0, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 9] = b4GapPatternWeight 0 6 9 * 0 :=
      b4GapContribution_from_row 2 0 6 9 0 row_02_00_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_09

theorem row_02_00_06_10 : b4RowContribution (![2, 2, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 18] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 18 = 30
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 396 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 18^2 = 396
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_10

theorem weighted_02_00_06_10 : b4RawGapContribution ![2, 0, 6, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 10] = b4GapPatternWeight 0 6 10 * 0 :=
      b4GapContribution_from_row 2 0 6 10 0 row_02_00_06_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_10

theorem row_02_00_06_11 : b4RowContribution (![2, 2, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 19] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 19 = 31
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 433 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 19^2 = 433
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_11

theorem weighted_02_00_06_11 : b4RawGapContribution ![2, 0, 6, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 11] = b4GapPatternWeight 0 6 11 * 0 :=
      b4GapContribution_from_row 2 0 6 11 0 row_02_00_06_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_11

theorem row_02_00_06_12 : b4RowContribution (![2, 2, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 20] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 20 = 32
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 472 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 20^2 = 472
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_12

theorem weighted_02_00_06_12 : b4RawGapContribution ![2, 0, 6, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 12] = b4GapPatternWeight 0 6 12 * 0 :=
      b4GapContribution_from_row 2 0 6 12 0 row_02_00_06_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_12

theorem row_02_00_06_13 : b4RowContribution (![2, 2, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 21] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 21 = 33
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 513 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 21^2 = 513
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_13

theorem weighted_02_00_06_13 : b4RawGapContribution ![2, 0, 6, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 13] = b4GapPatternWeight 0 6 13 * 0 :=
      b4GapContribution_from_row 2 0 6 13 0 row_02_00_06_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_13

theorem row_02_00_06_14 : b4RowContribution (![2, 2, 8, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 22] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 22 = 34
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 556 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 22^2 = 556
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_14

theorem weighted_02_00_06_14 : b4RawGapContribution ![2, 0, 6, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 14] = b4GapPatternWeight 0 6 14 * 0 :=
      b4GapContribution_from_row 2 0 6 14 0 row_02_00_06_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_14

theorem row_02_00_06_15 : b4RowContribution (![2, 2, 8, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 23] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 23 = 35
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 601 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 23^2 = 601
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_15

theorem weighted_02_00_06_15 : b4RawGapContribution ![2, 0, 6, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 15] = b4GapPatternWeight 0 6 15 * 0 :=
      b4GapContribution_from_row 2 0 6 15 0 row_02_00_06_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_15

theorem row_02_00_06_16 : b4RowContribution (![2, 2, 8, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 24] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 24 = 36
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 648 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 24^2 = 648
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_16

theorem weighted_02_00_06_16 : b4RawGapContribution ![2, 0, 6, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 16] = b4GapPatternWeight 0 6 16 * 0 :=
      b4GapContribution_from_row 2 0 6 16 0 row_02_00_06_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_16

theorem row_02_00_06_17 : b4RowContribution (![2, 2, 8, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 8, 25] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 8 + 25 = 37
    decide
  have hzsq : (∑ i, (((![2, 2, 8, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 697 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 8^2 + 25^2 = 697
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_06_17

theorem weighted_02_00_06_17 : b4RawGapContribution ![2, 0, 6, 17] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 6, 17] = b4GapPatternWeight 0 6 17 * 0 :=
      b4GapContribution_from_row 2 0 6 17 0 row_02_00_06_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_06_17

def dvalues_02_00_06 : Fin 18 → ℕ := ![0, 0, 0, 0, 972, 324, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_00_06

theorem dblock_02_00_06 : b4GapPatternDBlock 2 0 6 = 1296 := by
  calc
    b4GapPatternDBlock 2 0 6 = ∑ d : Fin 18, dvalues_02_00_06 d := by
      apply b4GapDBlock_of_rows 2 0 6 dvalues_02_00_06
      intro d
      fin_cases d
      · exact weighted_02_00_06_00
      · exact weighted_02_00_06_01
      · exact weighted_02_00_06_02
      · exact weighted_02_00_06_03
      · exact weighted_02_00_06_04
      · exact weighted_02_00_06_05
      · exact weighted_02_00_06_06
      · exact weighted_02_00_06_07
      · exact weighted_02_00_06_08
      · exact weighted_02_00_06_09
      · exact weighted_02_00_06_10
      · exact weighted_02_00_06_11
      · exact weighted_02_00_06_12
      · exact weighted_02_00_06_13
      · exact weighted_02_00_06_14
      · exact weighted_02_00_06_15
      · exact weighted_02_00_06_16
      · exact weighted_02_00_06_17
    _ = 1296 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_00_06

end Paper7MomentGapNumeric
