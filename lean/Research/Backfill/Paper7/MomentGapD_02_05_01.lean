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

theorem row_02_05_01_00 : b4RowContribution (![2, 7, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 8, 8] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 8 + 8 = 25
    decide
  have hzsq : (∑ i, (((![2, 7, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 181 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 8^2 + 8^2 = 181
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_01_00

theorem weighted_02_05_01_00 : b4RawGapContribution ![2, 5, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 1, 0] = b4GapPatternWeight 5 1 0 * 0 :=
      b4GapContribution_from_row 2 5 1 0 0 row_02_05_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_01_00

theorem row_02_05_01_01 : b4RowContribution (![2, 7, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 8, 9] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 8 + 9 = 26
    decide
  have hzsq : (∑ i, (((![2, 7, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 198 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 8^2 + 9^2 = 198
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_01_01

theorem weighted_02_05_01_01 : b4RawGapContribution ![2, 5, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 1, 1] = b4GapPatternWeight 5 1 1 * 0 :=
      b4GapContribution_from_row 2 5 1 1 0 row_02_05_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_01_01

theorem row_02_05_01_02 : b4RowContribution (![2, 7, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 8, 10] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 8 + 10 = 27
    decide
  have hzsq : (∑ i, (((![2, 7, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 217 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 8^2 + 10^2 = 217
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_01_02

theorem weighted_02_05_01_02 : b4RawGapContribution ![2, 5, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 1, 2] = b4GapPatternWeight 5 1 2 * 0 :=
      b4GapContribution_from_row 2 5 1 2 0 row_02_05_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_01_02

def layers_02_05_01_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 23, 23, 21, 18, 15, 12, 9, 6, 3, 1, 0], ![1, 4, 10, 19, 31, 46, 64, 85, 108, 131, 152, 170, 184, 193, 196, 193, 184, 170, 152]]
#print axioms Paper7MomentGapNumeric.layers_02_05_01_03

theorem cells_02_05_01_03 : QTableValid (![2, 7, 8, 11] : Fin 4 → ℕ) layers_02_05_01_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_05_01_03

theorem valid_02_05_01_03 :
    SparseRowValid (![2, 7, 8, 11] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_02_05_01_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 7, 8, 11] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 2 + 7 + 8 + 11 = 28
      decide
    have hzsq : (∑ i, (((![2, 7, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 238 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 7^2 + 8^2 + 11^2 = 238
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_05_01_03
#print axioms Paper7MomentGapNumeric.valid_02_05_01_03

def qvalues_02_05_01_03 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_05_01_03

theorem row_02_05_01_03 : b4RowContribution (![2, 7, 8, 11] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![2, 7, 8, 11] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_02_05_01_03) :=
      sparseRow_sound (![2, 7, 8, 11] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_02_05_01_03) valid_02_05_01_03
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_05_01_03 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.row_02_05_01_03

theorem weighted_02_05_01_03 : b4RawGapContribution ![2, 5, 1, 3] = 96 := by
  calc
    b4RawGapContribution ![2, 5, 1, 3] = b4GapPatternWeight 5 1 3 * 4 :=
      b4GapContribution_from_row 2 5 1 3 4 row_02_05_01_03
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_01_03

theorem row_02_05_01_04 : b4RowContribution (![2, 7, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 8, 12] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 8 + 12 = 29
    decide
  have hzsq : (∑ i, (((![2, 7, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 261 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 8^2 + 12^2 = 261
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_01_04

theorem weighted_02_05_01_04 : b4RawGapContribution ![2, 5, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 1, 4] = b4GapPatternWeight 5 1 4 * 0 :=
      b4GapContribution_from_row 2 5 1 4 0 row_02_05_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_01_04

def layers_02_05_01_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 23, 23, 21, 18, 15, 12, 9, 6, 3, 1, 0], ![1, 4, 10, 19, 31, 46, 64, 85, 108, 131, 152, 170, 185, 197, 205, 208, 205, 197, 185]]
#print axioms Paper7MomentGapNumeric.layers_02_05_01_05

theorem cells_02_05_01_05 : QTableValid (![2, 7, 8, 13] : Fin 4 → ℕ) layers_02_05_01_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_05_01_05

theorem valid_02_05_01_05 :
    SparseRowValid (![2, 7, 8, 13] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_05_01_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 7, 8, 13] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 2 + 7 + 8 + 13 = 30
      decide
    have hzsq : (∑ i, (((![2, 7, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 286 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 7^2 + 8^2 + 13^2 = 286
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_05_01_05
#print axioms Paper7MomentGapNumeric.valid_02_05_01_05

def qvalues_02_05_01_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_05_01_05

theorem row_02_05_01_05 : b4RowContribution (![2, 7, 8, 13] : Fin 4 → ℕ) = 31 := by
  calc
    b4RowContribution (![2, 7, 8, 13] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_02_05_01_05) :=
      sparseRow_sound (![2, 7, 8, 13] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_05_01_05) valid_02_05_01_05
    _ = 31 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_05_01_05 Q := by
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
        _ = 31 := by decide
#print axioms Paper7MomentGapNumeric.row_02_05_01_05

theorem weighted_02_05_01_05 : b4RawGapContribution ![2, 5, 1, 5] = 744 := by
  calc
    b4RawGapContribution ![2, 5, 1, 5] = b4GapPatternWeight 5 1 5 * 31 :=
      b4GapContribution_from_row 2 5 1 5 31 row_02_05_01_05
    _ = 744 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_01_05

theorem row_02_05_01_06 : b4RowContribution (![2, 7, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 8, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 8 + 14 = 31
    decide
  have hzsq : (∑ i, (((![2, 7, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 313 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 8^2 + 14^2 = 313
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_01_06

theorem weighted_02_05_01_06 : b4RawGapContribution ![2, 5, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 1, 6] = b4GapPatternWeight 5 1 6 * 0 :=
      b4GapContribution_from_row 2 5 1 6 0 row_02_05_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_01_06

theorem row_02_05_01_07 : b4RowContribution (![2, 7, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 8, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 8 + 15 = 32
    decide
  have hzsq : (∑ i, (((![2, 7, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 8^2 + 15^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_01_07

theorem weighted_02_05_01_07 : b4RawGapContribution ![2, 5, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 1, 7] = b4GapPatternWeight 5 1 7 * 0 :=
      b4GapContribution_from_row 2 5 1 7 0 row_02_05_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_01_07

theorem row_02_05_01_08 : b4RowContribution (![2, 7, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 8, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 8 + 16 = 33
    decide
  have hzsq : (∑ i, (((![2, 7, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 373 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 8^2 + 16^2 = 373
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_01_08

theorem weighted_02_05_01_08 : b4RawGapContribution ![2, 5, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 1, 8] = b4GapPatternWeight 5 1 8 * 0 :=
      b4GapContribution_from_row 2 5 1 8 0 row_02_05_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_01_08

theorem row_02_05_01_09 : b4RowContribution (![2, 7, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 8, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 8 + 17 = 34
    decide
  have hzsq : (∑ i, (((![2, 7, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 406 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 8^2 + 17^2 = 406
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_01_09

theorem weighted_02_05_01_09 : b4RawGapContribution ![2, 5, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 1, 9] = b4GapPatternWeight 5 1 9 * 0 :=
      b4GapContribution_from_row 2 5 1 9 0 row_02_05_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_01_09

theorem row_02_05_01_10 : b4RowContribution (![2, 7, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 8, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 8 + 18 = 35
    decide
  have hzsq : (∑ i, (((![2, 7, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 441 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 8^2 + 18^2 = 441
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_01_10

theorem weighted_02_05_01_10 : b4RawGapContribution ![2, 5, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 1, 10] = b4GapPatternWeight 5 1 10 * 0 :=
      b4GapContribution_from_row 2 5 1 10 0 row_02_05_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_01_10

theorem row_02_05_01_11 : b4RowContribution (![2, 7, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 8, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 8 + 19 = 36
    decide
  have hzsq : (∑ i, (((![2, 7, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 478 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 8^2 + 19^2 = 478
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_01_11

theorem weighted_02_05_01_11 : b4RawGapContribution ![2, 5, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 1, 11] = b4GapPatternWeight 5 1 11 * 0 :=
      b4GapContribution_from_row 2 5 1 11 0 row_02_05_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_01_11

theorem row_02_05_01_12 : b4RowContribution (![2, 7, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 8, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 8 + 20 = 37
    decide
  have hzsq : (∑ i, (((![2, 7, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 517 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 8^2 + 20^2 = 517
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_01_12

theorem weighted_02_05_01_12 : b4RawGapContribution ![2, 5, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 1, 12] = b4GapPatternWeight 5 1 12 * 0 :=
      b4GapContribution_from_row 2 5 1 12 0 row_02_05_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_01_12

def dvalues_02_05_01 : Fin 13 → ℕ := ![0, 0, 0, 96, 0, 744, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_05_01

theorem dblock_02_05_01 : b4GapPatternDBlock 2 5 1 = 840 := by
  calc
    b4GapPatternDBlock 2 5 1 = ∑ d : Fin 13, dvalues_02_05_01 d := by
      apply b4GapDBlock_of_rows 2 5 1 dvalues_02_05_01
      intro d
      fin_cases d
      · exact weighted_02_05_01_00
      · exact weighted_02_05_01_01
      · exact weighted_02_05_01_02
      · exact weighted_02_05_01_03
      · exact weighted_02_05_01_04
      · exact weighted_02_05_01_05
      · exact weighted_02_05_01_06
      · exact weighted_02_05_01_07
      · exact weighted_02_05_01_08
      · exact weighted_02_05_01_09
      · exact weighted_02_05_01_10
      · exact weighted_02_05_01_11
      · exact weighted_02_05_01_12
    _ = 840 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_05_01

end Paper7MomentGapNumeric
