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

theorem row_01_06_01_00 : b4RowContribution (![1, 7, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 8, 8] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 8 + 8 = 24
    decide
  have hzsq : (∑ i, (((![1, 7, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 178 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 8^2 + 8^2 = 178
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_01_00

theorem weighted_01_06_01_00 : b4RawGapContribution ![1, 6, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 1, 0] = b4GapPatternWeight 6 1 0 * 0 :=
      b4GapContribution_from_row 1 6 1 0 0 row_01_06_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_01_00

theorem row_01_06_01_01 : b4RowContribution (![1, 7, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 8, 9] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 8 + 9 = 25
    decide
  have hzsq : (∑ i, (((![1, 7, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 195 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 8^2 + 9^2 = 195
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_01_01

theorem weighted_01_06_01_01 : b4RawGapContribution ![1, 6, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 1, 1] = b4GapPatternWeight 6 1 1 * 0 :=
      b4GapContribution_from_row 1 6 1 1 0 row_01_06_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_01_01

theorem row_01_06_01_02 : b4RowContribution (![1, 7, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 8, 10] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 8 + 10 = 26
    decide
  have hzsq : (∑ i, (((![1, 7, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 214 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 8^2 + 10^2 = 214
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_01_02

theorem weighted_01_06_01_02 : b4RawGapContribution ![1, 6, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 1, 2] = b4GapPatternWeight 6 1 2 * 0 :=
      b4GapContribution_from_row 1 6 1 2 0 row_01_06_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_01_02

def layers_01_06_01_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 16, 15, 13, 11, 9, 7, 5, 3, 1, 0, 0], ![1, 4, 9, 16, 25, 36, 49, 64, 80, 95, 108, 119, 127, 131, 131, 127, 119, 108, 95]]
#print axioms Paper7MomentGapNumeric.layers_01_06_01_03

theorem cells_01_06_01_03 : QTableValid (![1, 7, 8, 11] : Fin 4 → ℕ) layers_01_06_01_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_06_01_03

theorem valid_01_06_01_03 :
    SparseRowValid (![1, 7, 8, 11] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_01_06_01_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 7, 8, 11] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 1 + 7 + 8 + 11 = 27
      decide
    have hzsq : (∑ i, (((![1, 7, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 235 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 7^2 + 8^2 + 11^2 = 235
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_06_01_03
#print axioms Paper7MomentGapNumeric.valid_01_06_01_03

def qvalues_01_06_01_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_06_01_03

theorem row_01_06_01_03 : b4RowContribution (![1, 7, 8, 11] : Fin 4 → ℕ) = 25 := by
  calc
    b4RowContribution (![1, 7, 8, 11] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_01_06_01_03) :=
      sparseRow_sound (![1, 7, 8, 11] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_01_06_01_03) valid_01_06_01_03
    _ = 25 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_06_01_03 Q := by
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
        _ = 25 := by decide
#print axioms Paper7MomentGapNumeric.row_01_06_01_03

theorem weighted_01_06_01_03 : b4RawGapContribution ![1, 6, 1, 3] = 600 := by
  calc
    b4RawGapContribution ![1, 6, 1, 3] = b4GapPatternWeight 6 1 3 * 25 :=
      b4GapContribution_from_row 1 6 1 3 25 row_01_06_01_03
    _ = 600 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_01_03

theorem row_01_06_01_04 : b4RowContribution (![1, 7, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 8, 12] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 8 + 12 = 28
    decide
  have hzsq : (∑ i, (((![1, 7, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 258 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 8^2 + 12^2 = 258
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_01_04

theorem weighted_01_06_01_04 : b4RawGapContribution ![1, 6, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 1, 4] = b4GapPatternWeight 6 1 4 * 0 :=
      b4GapContribution_from_row 1 6 1 4 0 row_01_06_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_01_04

def layers_01_06_01_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 16, 15, 13, 11, 9, 7, 5, 3, 1, 0, 0], ![1, 4, 9, 16, 25, 36, 49, 64, 80, 95, 108, 119, 128, 135, 139, 139, 135, 128, 119]]
#print axioms Paper7MomentGapNumeric.layers_01_06_01_05

theorem cells_01_06_01_05 : QTableValid (![1, 7, 8, 13] : Fin 4 → ℕ) layers_01_06_01_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_06_01_05

theorem valid_01_06_01_05 :
    SparseRowValid (![1, 7, 8, 13] : Fin 4 → ℕ) ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_06_01_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 7, 8, 13] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 1 + 7 + 8 + 13 = 29
      decide
    have hzsq : (∑ i, (((![1, 7, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 283 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 7^2 + 8^2 + 13^2 = 283
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_06_01_05
#print axioms Paper7MomentGapNumeric.valid_01_06_01_05

def qvalues_01_06_01_05 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_06_01_05

theorem row_01_06_01_05 : b4RowContribution (![1, 7, 8, 13] : Fin 4 → ℕ) = 68 := by
  calc
    b4RowContribution (![1, 7, 8, 13] : Fin 4 → ℕ) =
        sparseRowValue ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_06_01_05) :=
      sparseRow_sound (![1, 7, 8, 13] : Fin 4 → ℕ) ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_06_01_05) valid_01_06_01_05
    _ = 68 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_06_01_05 Q := by
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
        _ = 68 := by decide
#print axioms Paper7MomentGapNumeric.row_01_06_01_05

theorem weighted_01_06_01_05 : b4RawGapContribution ![1, 6, 1, 5] = 1632 := by
  calc
    b4RawGapContribution ![1, 6, 1, 5] = b4GapPatternWeight 6 1 5 * 68 :=
      b4GapContribution_from_row 1 6 1 5 68 row_01_06_01_05
    _ = 1632 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_01_05

theorem row_01_06_01_06 : b4RowContribution (![1, 7, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 8, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 8 + 14 = 30
    decide
  have hzsq : (∑ i, (((![1, 7, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 310 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 8^2 + 14^2 = 310
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_01_06

theorem weighted_01_06_01_06 : b4RawGapContribution ![1, 6, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 1, 6] = b4GapPatternWeight 6 1 6 * 0 :=
      b4GapContribution_from_row 1 6 1 6 0 row_01_06_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_01_06

theorem row_01_06_01_07 : b4RowContribution (![1, 7, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 8, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 8 + 15 = 31
    decide
  have hzsq : (∑ i, (((![1, 7, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 339 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 8^2 + 15^2 = 339
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_01_07

theorem weighted_01_06_01_07 : b4RawGapContribution ![1, 6, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 1, 7] = b4GapPatternWeight 6 1 7 * 0 :=
      b4GapContribution_from_row 1 6 1 7 0 row_01_06_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_01_07

theorem row_01_06_01_08 : b4RowContribution (![1, 7, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 8, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 8 + 16 = 32
    decide
  have hzsq : (∑ i, (((![1, 7, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 370 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 8^2 + 16^2 = 370
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_01_08

theorem weighted_01_06_01_08 : b4RawGapContribution ![1, 6, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 1, 8] = b4GapPatternWeight 6 1 8 * 0 :=
      b4GapContribution_from_row 1 6 1 8 0 row_01_06_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_01_08

theorem row_01_06_01_09 : b4RowContribution (![1, 7, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 8, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 8 + 17 = 33
    decide
  have hzsq : (∑ i, (((![1, 7, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 403 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 8^2 + 17^2 = 403
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_01_09

theorem weighted_01_06_01_09 : b4RawGapContribution ![1, 6, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 1, 9] = b4GapPatternWeight 6 1 9 * 0 :=
      b4GapContribution_from_row 1 6 1 9 0 row_01_06_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_01_09

theorem row_01_06_01_10 : b4RowContribution (![1, 7, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 8, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 8 + 18 = 34
    decide
  have hzsq : (∑ i, (((![1, 7, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 438 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 8^2 + 18^2 = 438
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_01_10

theorem weighted_01_06_01_10 : b4RawGapContribution ![1, 6, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 1, 10] = b4GapPatternWeight 6 1 10 * 0 :=
      b4GapContribution_from_row 1 6 1 10 0 row_01_06_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_01_10

theorem row_01_06_01_11 : b4RowContribution (![1, 7, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 8, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 8 + 19 = 35
    decide
  have hzsq : (∑ i, (((![1, 7, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 475 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 8^2 + 19^2 = 475
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_01_11

theorem weighted_01_06_01_11 : b4RawGapContribution ![1, 6, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 1, 11] = b4GapPatternWeight 6 1 11 * 0 :=
      b4GapContribution_from_row 1 6 1 11 0 row_01_06_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_01_11

theorem row_01_06_01_12 : b4RowContribution (![1, 7, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 8, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 8 + 20 = 36
    decide
  have hzsq : (∑ i, (((![1, 7, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 514 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 8^2 + 20^2 = 514
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_01_12

theorem weighted_01_06_01_12 : b4RawGapContribution ![1, 6, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 1, 12] = b4GapPatternWeight 6 1 12 * 0 :=
      b4GapContribution_from_row 1 6 1 12 0 row_01_06_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_01_12

theorem row_01_06_01_13 : b4RowContribution (![1, 7, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 8, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 8 + 21 = 37
    decide
  have hzsq : (∑ i, (((![1, 7, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 555 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 8^2 + 21^2 = 555
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_01_13

theorem weighted_01_06_01_13 : b4RawGapContribution ![1, 6, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 1, 13] = b4GapPatternWeight 6 1 13 * 0 :=
      b4GapContribution_from_row 1 6 1 13 0 row_01_06_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_01_13

def dvalues_01_06_01 : Fin 14 → ℕ := ![0, 0, 0, 600, 0, 1632, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_06_01

theorem dblock_01_06_01 : b4GapPatternDBlock 1 6 1 = 2232 := by
  calc
    b4GapPatternDBlock 1 6 1 = ∑ d : Fin 14, dvalues_01_06_01 d := by
      apply b4GapDBlock_of_rows 1 6 1 dvalues_01_06_01
      intro d
      fin_cases d
      · exact weighted_01_06_01_00
      · exact weighted_01_06_01_01
      · exact weighted_01_06_01_02
      · exact weighted_01_06_01_03
      · exact weighted_01_06_01_04
      · exact weighted_01_06_01_05
      · exact weighted_01_06_01_06
      · exact weighted_01_06_01_07
      · exact weighted_01_06_01_08
      · exact weighted_01_06_01_09
      · exact weighted_01_06_01_10
      · exact weighted_01_06_01_11
      · exact weighted_01_06_01_12
      · exact weighted_01_06_01_13
    _ = 2232 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_06_01

end Paper7MomentGapNumeric
