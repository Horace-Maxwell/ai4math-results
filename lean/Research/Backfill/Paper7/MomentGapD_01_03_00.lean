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

theorem row_01_03_00_00 : b4RowContribution (![1, 4, 4, 4] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 4] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 4 = 13
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 49 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 4^2 = 49
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_00

theorem weighted_01_03_00_00 : b4RawGapContribution ![1, 3, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 0] = b4GapPatternWeight 3 0 0 * 0 :=
      b4GapContribution_from_row 1 3 0 0 0 row_01_03_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_00

theorem row_01_03_00_01 : b4RowContribution (![1, 4, 4, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 5] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 5 = 14
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 58 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 5^2 = 58
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_01

theorem weighted_01_03_00_01 : b4RawGapContribution ![1, 3, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 1] = b4GapPatternWeight 3 0 1 * 0 :=
      b4GapContribution_from_row 1 3 0 1 0 row_01_03_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_01

theorem row_01_03_00_02 : b4RowContribution (![1, 4, 4, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 6] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 6 = 15
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 69 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 6^2 = 69
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_02

theorem weighted_01_03_00_02 : b4RawGapContribution ![1, 3, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 2] = b4GapPatternWeight 3 0 2 * 0 :=
      b4GapContribution_from_row 1 3 0 2 0 row_01_03_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_02

theorem row_01_03_00_03 : b4RowContribution (![1, 4, 4, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 7] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 7 = 16
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 82 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 7^2 = 82
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_03

theorem weighted_01_03_00_03 : b4RawGapContribution ![1, 3, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 3] = b4GapPatternWeight 3 0 3 * 0 :=
      b4GapContribution_from_row 1 3 0 3 0 row_01_03_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_03

theorem row_01_03_00_04 : b4RowContribution (![1, 4, 4, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 8] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 8 = 17
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 97 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 8^2 = 97
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_04

theorem weighted_01_03_00_04 : b4RawGapContribution ![1, 3, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 4] = b4GapPatternWeight 3 0 4 * 0 :=
      b4GapContribution_from_row 1 3 0 4 0 row_01_03_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_04

theorem row_01_03_00_05 : b4RowContribution (![1, 4, 4, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 9] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 9 = 18
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 114 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 9^2 = 114
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_05

theorem weighted_01_03_00_05 : b4RawGapContribution ![1, 3, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 5] = b4GapPatternWeight 3 0 5 * 0 :=
      b4GapContribution_from_row 1 3 0 5 0 row_01_03_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_05

theorem row_01_03_00_06 : b4RowContribution (![1, 4, 4, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 10] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 10 = 19
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 133 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 10^2 = 133
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_06

theorem weighted_01_03_00_06 : b4RawGapContribution ![1, 3, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 6] = b4GapPatternWeight 3 0 6 * 0 :=
      b4GapContribution_from_row 1 3 0 6 0 row_01_03_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_06

theorem row_01_03_00_07 : b4RowContribution (![1, 4, 4, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 11] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 11 = 20
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 154 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 11^2 = 154
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_07

theorem weighted_01_03_00_07 : b4RawGapContribution ![1, 3, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 7] = b4GapPatternWeight 3 0 7 * 0 :=
      b4GapContribution_from_row 1 3 0 7 0 row_01_03_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_07

theorem row_01_03_00_08 : b4RowContribution (![1, 4, 4, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 12] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 12 = 21
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 177 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 12^2 = 177
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_08

theorem weighted_01_03_00_08 : b4RawGapContribution ![1, 3, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 8] = b4GapPatternWeight 3 0 8 * 0 :=
      b4GapContribution_from_row 1 3 0 8 0 row_01_03_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_08

theorem row_01_03_00_09 : b4RowContribution (![1, 4, 4, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 13] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 13 = 22
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 202 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 13^2 = 202
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_09

theorem weighted_01_03_00_09 : b4RawGapContribution ![1, 3, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 9] = b4GapPatternWeight 3 0 9 * 0 :=
      b4GapContribution_from_row 1 3 0 9 0 row_01_03_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_09

def layers_01_03_00_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 34, 41, 46, 49, 50, 50, 50, 50, 50, 50, 49, 46, 41, 34]]
#print axioms Paper7MomentGapNumeric.layers_01_03_00_10

theorem cells_01_03_00_10 : QTableValid (![1, 4, 4, 14] : Fin 4 → ℕ) layers_01_03_00_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_00_10

theorem valid_01_03_00_10 :
    SparseRowValid (![1, 4, 4, 14] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_01_03_00_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 4, 14] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 4 + 14 = 23
      decide
    have hzsq : (∑ i, (((![1, 4, 4, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 229 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 4^2 + 14^2 = 229
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_00_10
#print axioms Paper7MomentGapNumeric.valid_01_03_00_10

def qvalues_01_03_00_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 46, 0, 0, 0, 0, 0, 50, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_00_10

theorem row_01_03_00_10 : b4RowContribution (![1, 4, 4, 14] : Fin 4 → ℕ) = 96 := by
  calc
    b4RowContribution (![1, 4, 4, 14] : Fin 4 → ℕ) =
        sparseRowValue ({7, 13} : Finset (Fin 19)) (fun _ => layers_01_03_00_10) :=
      sparseRow_sound (![1, 4, 4, 14] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_01_03_00_10) valid_01_03_00_10
    _ = 96 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_00_10 Q := by
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
        _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.row_01_03_00_10

theorem weighted_01_03_00_10 : b4RawGapContribution ![1, 3, 0, 10] = 1152 := by
  calc
    b4RawGapContribution ![1, 3, 0, 10] = b4GapPatternWeight 3 0 10 * 96 :=
      b4GapContribution_from_row 1 3 0 10 96 row_01_03_00_10
    _ = 1152 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_10

theorem row_01_03_00_11 : b4RowContribution (![1, 4, 4, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 15] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 15 = 24
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 258 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 15^2 = 258
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_11

theorem weighted_01_03_00_11 : b4RawGapContribution ![1, 3, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 11] = b4GapPatternWeight 3 0 11 * 0 :=
      b4GapContribution_from_row 1 3 0 11 0 row_01_03_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_11

def layers_01_03_00_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 34, 41, 46, 49, 50, 50, 50, 50, 50, 50, 50, 50, 49, 46]]
#print axioms Paper7MomentGapNumeric.layers_01_03_00_12

theorem cells_01_03_00_12 : QTableValid (![1, 4, 4, 16] : Fin 4 → ℕ) layers_01_03_00_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_00_12

theorem valid_01_03_00_12 :
    SparseRowValid (![1, 4, 4, 16] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_03_00_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 4, 16] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 4 + 16 = 25
      decide
    have hzsq : (∑ i, (((![1, 4, 4, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 289 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 4^2 + 16^2 = 289
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_00_12
#print axioms Paper7MomentGapNumeric.valid_01_03_00_12

def qvalues_01_03_00_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_00_12

theorem row_01_03_00_12 : b4RowContribution (![1, 4, 4, 16] : Fin 4 → ℕ) = 50 := by
  calc
    b4RowContribution (![1, 4, 4, 16] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_03_00_12) :=
      sparseRow_sound (![1, 4, 4, 16] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_03_00_12) valid_01_03_00_12
    _ = 50 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_00_12 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 50 := by decide
#print axioms Paper7MomentGapNumeric.row_01_03_00_12

theorem weighted_01_03_00_12 : b4RawGapContribution ![1, 3, 0, 12] = 600 := by
  calc
    b4RawGapContribution ![1, 3, 0, 12] = b4GapPatternWeight 3 0 12 * 50 :=
      b4GapContribution_from_row 1 3 0 12 50 row_01_03_00_12
    _ = 600 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_12

theorem row_01_03_00_13 : b4RowContribution (![1, 4, 4, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 17] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 17 = 26
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 322 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 17^2 = 322
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_13

theorem weighted_01_03_00_13 : b4RawGapContribution ![1, 3, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 13] = b4GapPatternWeight 3 0 13 * 0 :=
      b4GapContribution_from_row 1 3 0 13 0 row_01_03_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_13

theorem row_01_03_00_14 : b4RowContribution (![1, 4, 4, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 18] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 18 = 27
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 357 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 18^2 = 357
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_14

theorem weighted_01_03_00_14 : b4RawGapContribution ![1, 3, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 14] = b4GapPatternWeight 3 0 14 * 0 :=
      b4GapContribution_from_row 1 3 0 14 0 row_01_03_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_14

theorem row_01_03_00_15 : b4RowContribution (![1, 4, 4, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 19] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 19 = 28
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 394 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 19^2 = 394
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_15

theorem weighted_01_03_00_15 : b4RawGapContribution ![1, 3, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 15] = b4GapPatternWeight 3 0 15 * 0 :=
      b4GapContribution_from_row 1 3 0 15 0 row_01_03_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_15

theorem row_01_03_00_16 : b4RowContribution (![1, 4, 4, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 20] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 20 = 29
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 433 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 20^2 = 433
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_16

theorem weighted_01_03_00_16 : b4RawGapContribution ![1, 3, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 16] = b4GapPatternWeight 3 0 16 * 0 :=
      b4GapContribution_from_row 1 3 0 16 0 row_01_03_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_16

theorem row_01_03_00_17 : b4RowContribution (![1, 4, 4, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 21] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 21 = 30
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 474 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 21^2 = 474
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_17

theorem weighted_01_03_00_17 : b4RawGapContribution ![1, 3, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 17] = b4GapPatternWeight 3 0 17 * 0 :=
      b4GapContribution_from_row 1 3 0 17 0 row_01_03_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_17

theorem row_01_03_00_18 : b4RowContribution (![1, 4, 4, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 22] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 22 = 31
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 517 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 22^2 = 517
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_18

theorem weighted_01_03_00_18 : b4RawGapContribution ![1, 3, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 18] = b4GapPatternWeight 3 0 18 * 0 :=
      b4GapContribution_from_row 1 3 0 18 0 row_01_03_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_18

theorem row_01_03_00_19 : b4RowContribution (![1, 4, 4, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 23] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 23 = 32
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 562 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 23^2 = 562
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_19

theorem weighted_01_03_00_19 : b4RawGapContribution ![1, 3, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 19] = b4GapPatternWeight 3 0 19 * 0 :=
      b4GapContribution_from_row 1 3 0 19 0 row_01_03_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_19

theorem row_01_03_00_20 : b4RowContribution (![1, 4, 4, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 24] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 24 = 33
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 609 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 24^2 = 609
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_20

theorem weighted_01_03_00_20 : b4RawGapContribution ![1, 3, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 20] = b4GapPatternWeight 3 0 20 * 0 :=
      b4GapContribution_from_row 1 3 0 20 0 row_01_03_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_20

theorem row_01_03_00_21 : b4RowContribution (![1, 4, 4, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 25] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 25 = 34
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 658 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 25^2 = 658
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_21

theorem weighted_01_03_00_21 : b4RawGapContribution ![1, 3, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 21] = b4GapPatternWeight 3 0 21 * 0 :=
      b4GapContribution_from_row 1 3 0 21 0 row_01_03_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_21

theorem row_01_03_00_22 : b4RowContribution (![1, 4, 4, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 26] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 26 = 35
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 709 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 26^2 = 709
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_22

theorem weighted_01_03_00_22 : b4RawGapContribution ![1, 3, 0, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 22] = b4GapPatternWeight 3 0 22 * 0 :=
      b4GapContribution_from_row 1 3 0 22 0 row_01_03_00_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_22

theorem row_01_03_00_23 : b4RowContribution (![1, 4, 4, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 27] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 27 = 36
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 762 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 27^2 = 762
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_23

theorem weighted_01_03_00_23 : b4RawGapContribution ![1, 3, 0, 23] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 23] = b4GapPatternWeight 3 0 23 * 0 :=
      b4GapContribution_from_row 1 3 0 23 0 row_01_03_00_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_23

theorem row_01_03_00_24 : b4RowContribution (![1, 4, 4, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 4, 28] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 4 + 28 = 37
    decide
  have hzsq : (∑ i, (((![1, 4, 4, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 817 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 4^2 + 28^2 = 817
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_00_24

theorem weighted_01_03_00_24 : b4RawGapContribution ![1, 3, 0, 24] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 0, 24] = b4GapPatternWeight 3 0 24 * 0 :=
      b4GapContribution_from_row 1 3 0 24 0 row_01_03_00_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_00_24

def dvalues_01_03_00 : Fin 25 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1152, 0, 600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_03_00

theorem dblock_01_03_00 : b4GapPatternDBlock 1 3 0 = 1752 := by
  calc
    b4GapPatternDBlock 1 3 0 = ∑ d : Fin 25, dvalues_01_03_00 d := by
      apply b4GapDBlock_of_rows 1 3 0 dvalues_01_03_00
      intro d
      fin_cases d
      · exact weighted_01_03_00_00
      · exact weighted_01_03_00_01
      · exact weighted_01_03_00_02
      · exact weighted_01_03_00_03
      · exact weighted_01_03_00_04
      · exact weighted_01_03_00_05
      · exact weighted_01_03_00_06
      · exact weighted_01_03_00_07
      · exact weighted_01_03_00_08
      · exact weighted_01_03_00_09
      · exact weighted_01_03_00_10
      · exact weighted_01_03_00_11
      · exact weighted_01_03_00_12
      · exact weighted_01_03_00_13
      · exact weighted_01_03_00_14
      · exact weighted_01_03_00_15
      · exact weighted_01_03_00_16
      · exact weighted_01_03_00_17
      · exact weighted_01_03_00_18
      · exact weighted_01_03_00_19
      · exact weighted_01_03_00_20
      · exact weighted_01_03_00_21
      · exact weighted_01_03_00_22
      · exact weighted_01_03_00_23
      · exact weighted_01_03_00_24
    _ = 1752 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_03_00

end Paper7MomentGapNumeric
