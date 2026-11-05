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

theorem row_06_01_00_00 : b4RowContribution (![6, 7, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 7, 7] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 7 + 7 = 27
    decide
  have hzsq : (∑ i, (((![6, 7, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 183 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 7^2 + 7^2 = 183
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_00_00

theorem weighted_06_01_00_00 : b4RawGapContribution ![6, 1, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 0, 0] = b4GapPatternWeight 1 0 0 * 0 :=
      b4GapContribution_from_row 6 1 0 0 0 row_06_01_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_00_00

theorem row_06_01_00_01 : b4RowContribution (![6, 7, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 7, 8] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 7 + 8 = 28
    decide
  have hzsq : (∑ i, (((![6, 7, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 198 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 7^2 + 8^2 = 198
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_00_01

theorem weighted_06_01_00_01 : b4RawGapContribution ![6, 1, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 0, 1] = b4GapPatternWeight 1 0 1 * 0 :=
      b4GapContribution_from_row 6 1 0 1 0 row_06_01_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_00_01

theorem row_06_01_00_02 : b4RowContribution (![6, 7, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 7, 9] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 7 + 9 = 29
    decide
  have hzsq : (∑ i, (((![6, 7, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 215 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 7^2 + 9^2 = 215
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_00_02

theorem weighted_06_01_00_02 : b4RawGapContribution ![6, 1, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 0, 2] = b4GapPatternWeight 1 0 2 * 0 :=
      b4GapContribution_from_row 6 1 0 2 0 row_06_01_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_00_02

def layers_06_01_00_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 35, 40, 43, 44, 43, 40, 35, 28, 21, 15, 10, 6], ![1, 4, 10, 20, 35, 56, 84, 119, 159, 202, 246, 288, 325, 354, 372, 378, 372, 354, 325]]
#print axioms Paper7MomentGapNumeric.layers_06_01_00_03

theorem cells_06_01_00_03 : QTableValid (![6, 7, 7, 10] : Fin 4 → ℕ) layers_06_01_00_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_06_01_00_03

theorem valid_06_01_00_03 :
    SparseRowValid (![6, 7, 7, 10] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_06_01_00_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![6, 7, 7, 10] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 6 + 7 + 7 + 10 = 30
      decide
    have hzsq : (∑ i, (((![6, 7, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 234 := by
      rw [Fin.sum_univ_four]
      change (6 : ℤ)^2 + 7^2 + 7^2 + 10^2 = 234
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_06_01_00_03
#print axioms Paper7MomentGapNumeric.valid_06_01_00_03

def qvalues_06_01_00_03 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_06_01_00_03

theorem row_06_01_00_03 : b4RowContribution (![6, 7, 7, 10] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![6, 7, 7, 10] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_06_01_00_03) :=
      sparseRow_sound (![6, 7, 7, 10] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_06_01_00_03) valid_06_01_00_03
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_06_01_00_03 Q := by
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
#print axioms Paper7MomentGapNumeric.row_06_01_00_03

theorem weighted_06_01_00_03 : b4RawGapContribution ![6, 1, 0, 3] = 12 := by
  calc
    b4RawGapContribution ![6, 1, 0, 3] = b4GapPatternWeight 1 0 3 * 1 :=
      b4GapContribution_from_row 6 1 0 3 1 row_06_01_00_03
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_00_03

theorem row_06_01_00_04 : b4RowContribution (![6, 7, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 7, 11] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 7 + 11 = 31
    decide
  have hzsq : (∑ i, (((![6, 7, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 255 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 7^2 + 11^2 = 255
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_00_04

theorem weighted_06_01_00_04 : b4RawGapContribution ![6, 1, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 0, 4] = b4GapPatternWeight 1 0 4 * 0 :=
      b4GapContribution_from_row 6 1 0 4 0 row_06_01_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_00_04

def layers_06_01_00_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 35, 40, 43, 44, 43, 40, 35, 28, 21, 15, 10, 6], ![1, 4, 10, 20, 35, 56, 84, 119, 159, 202, 246, 289, 329, 363, 388, 403, 408, 403, 388]]
#print axioms Paper7MomentGapNumeric.layers_06_01_00_05

theorem cells_06_01_00_05 : QTableValid (![6, 7, 7, 12] : Fin 4 → ℕ) layers_06_01_00_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_06_01_00_05

theorem valid_06_01_00_05 :
    SparseRowValid (![6, 7, 7, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_06_01_00_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![6, 7, 7, 12] : Fin 4 → ℕ) i) = 32 := by
      rw [Fin.sum_univ_four]
      change 6 + 7 + 7 + 12 = 32
      decide
    have hzsq : (∑ i, (((![6, 7, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 278 := by
      rw [Fin.sum_univ_four]
      change (6 : ℤ)^2 + 7^2 + 7^2 + 12^2 = 278
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_06_01_00_05
#print axioms Paper7MomentGapNumeric.valid_06_01_00_05

def qvalues_06_01_00_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_06_01_00_05

theorem row_06_01_00_05 : b4RowContribution (![6, 7, 7, 12] : Fin 4 → ℕ) = 56 := by
  calc
    b4RowContribution (![6, 7, 7, 12] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_06_01_00_05) :=
      sparseRow_sound (![6, 7, 7, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_06_01_00_05) valid_06_01_00_05
    _ = 56 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_06_01_00_05 Q := by
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
        _ = 56 := by decide
#print axioms Paper7MomentGapNumeric.row_06_01_00_05

theorem weighted_06_01_00_05 : b4RawGapContribution ![6, 1, 0, 5] = 672 := by
  calc
    b4RawGapContribution ![6, 1, 0, 5] = b4GapPatternWeight 1 0 5 * 56 :=
      b4GapContribution_from_row 6 1 0 5 56 row_06_01_00_05
    _ = 672 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_00_05

theorem row_06_01_00_06 : b4RowContribution (![6, 7, 7, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 7, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 7 + 13 = 33
    decide
  have hzsq : (∑ i, (((![6, 7, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 303 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 7^2 + 13^2 = 303
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_00_06

theorem weighted_06_01_00_06 : b4RawGapContribution ![6, 1, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 0, 6] = b4GapPatternWeight 1 0 6 * 0 :=
      b4GapContribution_from_row 6 1 0 6 0 row_06_01_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_00_06

theorem row_06_01_00_07 : b4RowContribution (![6, 7, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 7, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 7 + 14 = 34
    decide
  have hzsq : (∑ i, (((![6, 7, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 330 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 7^2 + 14^2 = 330
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_00_07

theorem weighted_06_01_00_07 : b4RawGapContribution ![6, 1, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 0, 7] = b4GapPatternWeight 1 0 7 * 0 :=
      b4GapContribution_from_row 6 1 0 7 0 row_06_01_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_00_07

theorem row_06_01_00_08 : b4RowContribution (![6, 7, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 7, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 7 + 15 = 35
    decide
  have hzsq : (∑ i, (((![6, 7, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 359 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 7^2 + 15^2 = 359
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_00_08

theorem weighted_06_01_00_08 : b4RawGapContribution ![6, 1, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 0, 8] = b4GapPatternWeight 1 0 8 * 0 :=
      b4GapContribution_from_row 6 1 0 8 0 row_06_01_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_00_08

theorem row_06_01_00_09 : b4RowContribution (![6, 7, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 7, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 7 + 16 = 36
    decide
  have hzsq : (∑ i, (((![6, 7, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 7^2 + 16^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_00_09

theorem weighted_06_01_00_09 : b4RawGapContribution ![6, 1, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 0, 9] = b4GapPatternWeight 1 0 9 * 0 :=
      b4GapContribution_from_row 6 1 0 9 0 row_06_01_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_00_09

theorem row_06_01_00_10 : b4RowContribution (![6, 7, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 7, 7, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 6 + 7 + 7 + 17 = 37
    decide
  have hzsq : (∑ i, (((![6, 7, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 423 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 7^2 + 7^2 + 17^2 = 423
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_01_00_10

theorem weighted_06_01_00_10 : b4RawGapContribution ![6, 1, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![6, 1, 0, 10] = b4GapPatternWeight 1 0 10 * 0 :=
      b4GapContribution_from_row 6 1 0 10 0 row_06_01_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_01_00_10

def dvalues_06_01_00 : Fin 11 → ℕ := ![0, 0, 0, 12, 0, 672, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_06_01_00

theorem dblock_06_01_00 : b4GapPatternDBlock 6 1 0 = 684 := by
  calc
    b4GapPatternDBlock 6 1 0 = ∑ d : Fin 11, dvalues_06_01_00 d := by
      apply b4GapDBlock_of_rows 6 1 0 dvalues_06_01_00
      intro d
      fin_cases d
      · exact weighted_06_01_00_00
      · exact weighted_06_01_00_01
      · exact weighted_06_01_00_02
      · exact weighted_06_01_00_03
      · exact weighted_06_01_00_04
      · exact weighted_06_01_00_05
      · exact weighted_06_01_00_06
      · exact weighted_06_01_00_07
      · exact weighted_06_01_00_08
      · exact weighted_06_01_00_09
      · exact weighted_06_01_00_10
    _ = 684 := by decide
#print axioms Paper7MomentGapNumeric.dblock_06_01_00

end Paper7MomentGapNumeric
