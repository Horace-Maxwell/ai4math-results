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

theorem row_04_01_02_00 : b4RowContribution (![4, 5, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 7, 7] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 7 + 7 = 23
    decide
  have hzsq : (∑ i, (((![4, 5, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 139 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 7^2 + 7^2 = 139
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_02_00

theorem weighted_04_01_02_00 : b4RawGapContribution ![4, 1, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 2, 0] = b4GapPatternWeight 1 2 0 * 0 :=
      b4GapContribution_from_row 4 1 2 0 0 row_04_01_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_00

theorem row_04_01_02_01 : b4RowContribution (![4, 5, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 7, 8] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 7 + 8 = 24
    decide
  have hzsq : (∑ i, (((![4, 5, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 154 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 7^2 + 8^2 = 154
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_02_01

theorem weighted_04_01_02_01 : b4RawGapContribution ![4, 1, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 2, 1] = b4GapPatternWeight 1 2 1 * 0 :=
      b4GapContribution_from_row 4 1 2 1 0 row_04_01_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_01

theorem row_04_01_02_02 : b4RowContribution (![4, 5, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 7, 9] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 7 + 9 = 25
    decide
  have hzsq : (∑ i, (((![4, 5, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 171 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 7^2 + 9^2 = 171
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_02_02

theorem weighted_04_01_02_02 : b4RawGapContribution ![4, 1, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 2, 2] = b4GapPatternWeight 1 2 2 * 0 :=
      b4GapContribution_from_row 4 1 2 2 0 row_04_01_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_02

theorem row_04_01_02_03 : b4RowContribution (![4, 5, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 7, 10] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 7 + 10 = 26
    decide
  have hzsq : (∑ i, (((![4, 5, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 190 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 7^2 + 10^2 = 190
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_02_03

theorem weighted_04_01_02_03 : b4RawGapContribution ![4, 1, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 2, 3] = b4GapPatternWeight 1 2 3 * 0 :=
      b4GapContribution_from_row 4 1 2 3 0 row_04_01_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_03

theorem row_04_01_02_04 : b4RowContribution (![4, 5, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 7, 11] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 7 + 11 = 27
    decide
  have hzsq : (∑ i, (((![4, 5, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 211 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 7^2 + 11^2 = 211
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_02_04

theorem weighted_04_01_02_04 : b4RawGapContribution ![4, 1, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 2, 4] = b4GapPatternWeight 1 2 4 * 0 :=
      b4GapContribution_from_row 4 1 2 4 0 row_04_01_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_04

def layers_04_01_02_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 24, 27, 28, 27, 24, 20, 15, 10, 6, 3, 1, 0, 0], ![1, 4, 10, 20, 35, 55, 79, 106, 134, 161, 185, 205, 220, 229, 232, 229, 220, 205, 185]]
#print axioms Paper7MomentGapNumeric.layers_04_01_02_05

theorem cells_04_01_02_05 : QTableValid (![4, 5, 7, 12] : Fin 4 → ℕ) layers_04_01_02_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_01_02_05

theorem valid_04_01_02_05 :
    SparseRowValid (![4, 5, 7, 12] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_04_01_02_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 5, 7, 12] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 4 + 5 + 7 + 12 = 28
      decide
    have hzsq : (∑ i, (((![4, 5, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 234 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 5^2 + 7^2 + 12^2 = 234
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_01_02_05
#print axioms Paper7MomentGapNumeric.valid_04_01_02_05

def qvalues_04_01_02_05 : Fin 19 → ℕ := ![0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_01_02_05

theorem row_04_01_02_05 : b4RowContribution (![4, 5, 7, 12] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![4, 5, 7, 12] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_04_01_02_05) :=
      sparseRow_sound (![4, 5, 7, 12] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_04_01_02_05) valid_04_01_02_05
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_01_02_05 Q := by
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
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_04_01_02_05

theorem weighted_04_01_02_05 : b4RawGapContribution ![4, 1, 2, 5] = 480 := by
  calc
    b4RawGapContribution ![4, 1, 2, 5] = b4GapPatternWeight 1 2 5 * 20 :=
      b4GapContribution_from_row 4 1 2 5 20 row_04_01_02_05
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_05

theorem row_04_01_02_06 : b4RowContribution (![4, 5, 7, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 7, 13] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 7 + 13 = 29
    decide
  have hzsq : (∑ i, (((![4, 5, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 259 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 7^2 + 13^2 = 259
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_02_06

theorem weighted_04_01_02_06 : b4RawGapContribution ![4, 1, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 2, 6] = b4GapPatternWeight 1 2 6 * 0 :=
      b4GapContribution_from_row 4 1 2 6 0 row_04_01_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_06

def layers_04_01_02_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 24, 27, 28, 27, 24, 20, 15, 10, 6, 3, 1, 0, 0], ![1, 4, 10, 20, 35, 55, 79, 106, 134, 161, 185, 205, 220, 230, 236, 238, 236, 230, 220]]
#print axioms Paper7MomentGapNumeric.layers_04_01_02_07

theorem cells_04_01_02_07 : QTableValid (![4, 5, 7, 14] : Fin 4 → ℕ) layers_04_01_02_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_01_02_07

theorem valid_04_01_02_07 :
    SparseRowValid (![4, 5, 7, 14] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_04_01_02_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 5, 7, 14] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 4 + 5 + 7 + 14 = 30
      decide
    have hzsq : (∑ i, (((![4, 5, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 286 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 5^2 + 7^2 + 14^2 = 286
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_01_02_07
#print axioms Paper7MomentGapNumeric.valid_04_01_02_07

def qvalues_04_01_02_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_01_02_07

theorem row_04_01_02_07 : b4RowContribution (![4, 5, 7, 14] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![4, 5, 7, 14] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_04_01_02_07) :=
      sparseRow_sound (![4, 5, 7, 14] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_04_01_02_07) valid_04_01_02_07
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_01_02_07 Q := by
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
        _ = 35 := by decide
#print axioms Paper7MomentGapNumeric.row_04_01_02_07

theorem weighted_04_01_02_07 : b4RawGapContribution ![4, 1, 2, 7] = 840 := by
  calc
    b4RawGapContribution ![4, 1, 2, 7] = b4GapPatternWeight 1 2 7 * 35 :=
      b4GapContribution_from_row 4 1 2 7 35 row_04_01_02_07
    _ = 840 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_07

theorem row_04_01_02_08 : b4RowContribution (![4, 5, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 7, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 7 + 15 = 31
    decide
  have hzsq : (∑ i, (((![4, 5, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 315 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 7^2 + 15^2 = 315
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_02_08

theorem weighted_04_01_02_08 : b4RawGapContribution ![4, 1, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 2, 8] = b4GapPatternWeight 1 2 8 * 0 :=
      b4GapContribution_from_row 4 1 2 8 0 row_04_01_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_08

theorem row_04_01_02_09 : b4RowContribution (![4, 5, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 7, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 7 + 16 = 32
    decide
  have hzsq : (∑ i, (((![4, 5, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 346 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 7^2 + 16^2 = 346
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_02_09

theorem weighted_04_01_02_09 : b4RawGapContribution ![4, 1, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 2, 9] = b4GapPatternWeight 1 2 9 * 0 :=
      b4GapContribution_from_row 4 1 2 9 0 row_04_01_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_09

theorem row_04_01_02_10 : b4RowContribution (![4, 5, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 7, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 7 + 17 = 33
    decide
  have hzsq : (∑ i, (((![4, 5, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 379 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 7^2 + 17^2 = 379
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_02_10

theorem weighted_04_01_02_10 : b4RawGapContribution ![4, 1, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 2, 10] = b4GapPatternWeight 1 2 10 * 0 :=
      b4GapContribution_from_row 4 1 2 10 0 row_04_01_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_10

theorem row_04_01_02_11 : b4RowContribution (![4, 5, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 7, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 7 + 18 = 34
    decide
  have hzsq : (∑ i, (((![4, 5, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 414 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 7^2 + 18^2 = 414
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_02_11

theorem weighted_04_01_02_11 : b4RawGapContribution ![4, 1, 2, 11] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 2, 11] = b4GapPatternWeight 1 2 11 * 0 :=
      b4GapContribution_from_row 4 1 2 11 0 row_04_01_02_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_11

theorem row_04_01_02_12 : b4RowContribution (![4, 5, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 7, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 7 + 19 = 35
    decide
  have hzsq : (∑ i, (((![4, 5, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 451 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 7^2 + 19^2 = 451
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_02_12

theorem weighted_04_01_02_12 : b4RawGapContribution ![4, 1, 2, 12] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 2, 12] = b4GapPatternWeight 1 2 12 * 0 :=
      b4GapContribution_from_row 4 1 2 12 0 row_04_01_02_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_12

theorem row_04_01_02_13 : b4RowContribution (![4, 5, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 7, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 7 + 20 = 36
    decide
  have hzsq : (∑ i, (((![4, 5, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 490 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 7^2 + 20^2 = 490
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_02_13

theorem weighted_04_01_02_13 : b4RawGapContribution ![4, 1, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 2, 13] = b4GapPatternWeight 1 2 13 * 0 :=
      b4GapContribution_from_row 4 1 2 13 0 row_04_01_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_13

theorem row_04_01_02_14 : b4RowContribution (![4, 5, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 7, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 7 + 21 = 37
    decide
  have hzsq : (∑ i, (((![4, 5, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 531 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 7^2 + 21^2 = 531
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_02_14

theorem weighted_04_01_02_14 : b4RawGapContribution ![4, 1, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 2, 14] = b4GapPatternWeight 1 2 14 * 0 :=
      b4GapContribution_from_row 4 1 2 14 0 row_04_01_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_02_14

def dvalues_04_01_02 : Fin 15 → ℕ := ![0, 0, 0, 0, 0, 480, 0, 840, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_01_02

theorem dblock_04_01_02 : b4GapPatternDBlock 4 1 2 = 1320 := by
  calc
    b4GapPatternDBlock 4 1 2 = ∑ d : Fin 15, dvalues_04_01_02 d := by
      apply b4GapDBlock_of_rows 4 1 2 dvalues_04_01_02
      intro d
      fin_cases d
      · exact weighted_04_01_02_00
      · exact weighted_04_01_02_01
      · exact weighted_04_01_02_02
      · exact weighted_04_01_02_03
      · exact weighted_04_01_02_04
      · exact weighted_04_01_02_05
      · exact weighted_04_01_02_06
      · exact weighted_04_01_02_07
      · exact weighted_04_01_02_08
      · exact weighted_04_01_02_09
      · exact weighted_04_01_02_10
      · exact weighted_04_01_02_11
      · exact weighted_04_01_02_12
      · exact weighted_04_01_02_13
      · exact weighted_04_01_02_14
    _ = 1320 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_01_02

end Paper7MomentGapNumeric
