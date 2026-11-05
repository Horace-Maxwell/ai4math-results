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

theorem row_02_02_01_00 : b4RowContribution (![2, 4, 5, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 5] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 5 = 16
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 70 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 5^2 = 70
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_00

theorem weighted_02_02_01_00 : b4RawGapContribution ![2, 2, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 0] = b4GapPatternWeight 2 1 0 * 0 :=
      b4GapContribution_from_row 2 2 1 0 0 row_02_02_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_00

theorem row_02_02_01_01 : b4RowContribution (![2, 4, 5, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 6] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 6 = 17
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 81 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 6^2 = 81
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_01

theorem weighted_02_02_01_01 : b4RawGapContribution ![2, 2, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 1] = b4GapPatternWeight 2 1 1 * 0 :=
      b4GapContribution_from_row 2 2 1 1 0 row_02_02_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_01

theorem row_02_02_01_02 : b4RowContribution (![2, 4, 5, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 7] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 7 = 18
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 94 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 7^2 = 94
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_02

theorem weighted_02_02_01_02 : b4RawGapContribution ![2, 2, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 2] = b4GapPatternWeight 2 1 2 * 0 :=
      b4GapContribution_from_row 2 2 1 2 0 row_02_02_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_02

theorem row_02_02_01_03 : b4RowContribution (![2, 4, 5, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 8] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 8 = 19
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 109 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 8^2 = 109
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_03

theorem weighted_02_02_01_03 : b4RawGapContribution ![2, 2, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 3] = b4GapPatternWeight 2 1 3 * 0 :=
      b4GapContribution_from_row 2 2 1 3 0 row_02_02_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_03

theorem row_02_02_01_04 : b4RowContribution (![2, 4, 5, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 9] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 9 = 20
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 126 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 9^2 = 126
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_04

theorem weighted_02_02_01_04 : b4RawGapContribution ![2, 2, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 4] = b4GapPatternWeight 2 1 4 * 0 :=
      b4GapContribution_from_row 2 2 1 4 0 row_02_02_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_04

theorem row_02_02_01_05 : b4RowContribution (![2, 4, 5, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 10] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 10 = 21
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 145 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 10^2 = 145
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_05

theorem weighted_02_02_01_05 : b4RawGapContribution ![2, 2, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 5] = b4GapPatternWeight 2 1 5 * 0 :=
      b4GapContribution_from_row 2 2 1 5 0 row_02_02_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_05

theorem row_02_02_01_06 : b4RowContribution (![2, 4, 5, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 11] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 11 = 22
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 166 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 11^2 = 166
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_06

theorem weighted_02_02_01_06 : b4RawGapContribution ![2, 2, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 6] = b4GapPatternWeight 2 1 6 * 0 :=
      b4GapContribution_from_row 2 2 1 6 0 row_02_02_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_06

theorem row_02_02_01_07 : b4RowContribution (![2, 4, 5, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 12] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 12 = 23
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 189 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 12^2 = 189
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_07

theorem weighted_02_02_01_07 : b4RawGapContribution ![2, 2, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 7] = b4GapPatternWeight 2 1 7 * 0 :=
      b4GapContribution_from_row 2 2 1 7 0 row_02_02_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_07

def layers_02_02_01_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 14, 14, 12, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 31, 45, 59, 71, 80, 86, 89, 90, 90, 90, 89, 86, 80, 71, 59]]
#print axioms Paper7MomentGapNumeric.layers_02_02_01_08

theorem cells_02_02_01_08 : QTableValid (![2, 4, 5, 13] : Fin 4 → ℕ) layers_02_02_01_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_02_01_08

theorem valid_02_02_01_08 :
    SparseRowValid (![2, 4, 5, 13] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_02_02_01_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 4, 5, 13] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 2 + 4 + 5 + 13 = 24
      decide
    have hzsq : (∑ i, (((![2, 4, 5, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 214 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 4^2 + 5^2 + 13^2 = 214
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_02_01_08
#print axioms Paper7MomentGapNumeric.valid_02_02_01_08

def qvalues_02_02_01_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 90, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_02_01_08

theorem row_02_02_01_08 : b4RowContribution (![2, 4, 5, 13] : Fin 4 → ℕ) = 90 := by
  calc
    b4RowContribution (![2, 4, 5, 13] : Fin 4 → ℕ) =
        sparseRowValue ({13} : Finset (Fin 19)) (fun _ => layers_02_02_01_08) :=
      sparseRow_sound (![2, 4, 5, 13] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_02_02_01_08) valid_02_02_01_08
    _ = 90 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_02_01_08 Q := by
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
        _ = 90 := by decide
#print axioms Paper7MomentGapNumeric.row_02_02_01_08

theorem weighted_02_02_01_08 : b4RawGapContribution ![2, 2, 1, 8] = 2160 := by
  calc
    b4RawGapContribution ![2, 2, 1, 8] = b4GapPatternWeight 2 1 8 * 90 :=
      b4GapContribution_from_row 2 2 1 8 90 row_02_02_01_08
    _ = 2160 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_08

def layers_02_02_01_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 14, 14, 12, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 31, 45, 59, 71, 80, 86, 89, 90, 90, 90, 90, 89, 86, 80, 71]]
#print axioms Paper7MomentGapNumeric.layers_02_02_01_09

theorem cells_02_02_01_09 : QTableValid (![2, 4, 5, 14] : Fin 4 → ℕ) layers_02_02_01_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_02_01_09

theorem valid_02_02_01_09 :
    SparseRowValid (![2, 4, 5, 14] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_02_01_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 4, 5, 14] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 2 + 4 + 5 + 14 = 25
      decide
    have hzsq : (∑ i, (((![2, 4, 5, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 241 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 4^2 + 5^2 + 14^2 = 241
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_02_01_09
#print axioms Paper7MomentGapNumeric.valid_02_02_01_09

def qvalues_02_02_01_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_02_01_09

theorem row_02_02_01_09 : b4RowContribution (![2, 4, 5, 14] : Fin 4 → ℕ) = 31 := by
  calc
    b4RowContribution (![2, 4, 5, 14] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_02_02_01_09) :=
      sparseRow_sound (![2, 4, 5, 14] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_02_01_09) valid_02_02_01_09
    _ = 31 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_02_01_09 Q := by
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
#print axioms Paper7MomentGapNumeric.row_02_02_01_09

theorem weighted_02_02_01_09 : b4RawGapContribution ![2, 2, 1, 9] = 744 := by
  calc
    b4RawGapContribution ![2, 2, 1, 9] = b4GapPatternWeight 2 1 9 * 31 :=
      b4GapContribution_from_row 2 2 1 9 31 row_02_02_01_09
    _ = 744 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_09

theorem row_02_02_01_10 : b4RowContribution (![2, 4, 5, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 15] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 15 = 26
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 15^2 = 270
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_10

theorem weighted_02_02_01_10 : b4RawGapContribution ![2, 2, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 10] = b4GapPatternWeight 2 1 10 * 0 :=
      b4GapContribution_from_row 2 2 1 10 0 row_02_02_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_10

theorem row_02_02_01_11 : b4RowContribution (![2, 4, 5, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 16] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 16 = 27
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 301 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 16^2 = 301
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_11

theorem weighted_02_02_01_11 : b4RawGapContribution ![2, 2, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 11] = b4GapPatternWeight 2 1 11 * 0 :=
      b4GapContribution_from_row 2 2 1 11 0 row_02_02_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_11

theorem row_02_02_01_12 : b4RowContribution (![2, 4, 5, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 17] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 17 = 28
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 334 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 17^2 = 334
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_12

theorem weighted_02_02_01_12 : b4RawGapContribution ![2, 2, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 12] = b4GapPatternWeight 2 1 12 * 0 :=
      b4GapContribution_from_row 2 2 1 12 0 row_02_02_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_12

theorem row_02_02_01_13 : b4RowContribution (![2, 4, 5, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 18] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 18 = 29
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 369 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 18^2 = 369
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_13

theorem weighted_02_02_01_13 : b4RawGapContribution ![2, 2, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 13] = b4GapPatternWeight 2 1 13 * 0 :=
      b4GapContribution_from_row 2 2 1 13 0 row_02_02_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_13

theorem row_02_02_01_14 : b4RowContribution (![2, 4, 5, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 19] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 19 = 30
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 406 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 19^2 = 406
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_14

theorem weighted_02_02_01_14 : b4RawGapContribution ![2, 2, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 14] = b4GapPatternWeight 2 1 14 * 0 :=
      b4GapContribution_from_row 2 2 1 14 0 row_02_02_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_14

theorem row_02_02_01_15 : b4RowContribution (![2, 4, 5, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 20] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 20 = 31
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 445 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 20^2 = 445
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_15

theorem weighted_02_02_01_15 : b4RawGapContribution ![2, 2, 1, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 15] = b4GapPatternWeight 2 1 15 * 0 :=
      b4GapContribution_from_row 2 2 1 15 0 row_02_02_01_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_15

theorem row_02_02_01_16 : b4RowContribution (![2, 4, 5, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 21] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 21 = 32
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 486 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 21^2 = 486
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_16

theorem weighted_02_02_01_16 : b4RawGapContribution ![2, 2, 1, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 16] = b4GapPatternWeight 2 1 16 * 0 :=
      b4GapContribution_from_row 2 2 1 16 0 row_02_02_01_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_16

theorem row_02_02_01_17 : b4RowContribution (![2, 4, 5, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 22] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 22 = 33
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 529 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 22^2 = 529
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_17

theorem weighted_02_02_01_17 : b4RawGapContribution ![2, 2, 1, 17] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 17] = b4GapPatternWeight 2 1 17 * 0 :=
      b4GapContribution_from_row 2 2 1 17 0 row_02_02_01_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_17

theorem row_02_02_01_18 : b4RowContribution (![2, 4, 5, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 23] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 23 = 34
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 574 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 23^2 = 574
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_18

theorem weighted_02_02_01_18 : b4RawGapContribution ![2, 2, 1, 18] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 18] = b4GapPatternWeight 2 1 18 * 0 :=
      b4GapContribution_from_row 2 2 1 18 0 row_02_02_01_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_18

theorem row_02_02_01_19 : b4RowContribution (![2, 4, 5, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 24] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 24 = 35
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 621 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 24^2 = 621
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_19

theorem weighted_02_02_01_19 : b4RawGapContribution ![2, 2, 1, 19] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 19] = b4GapPatternWeight 2 1 19 * 0 :=
      b4GapContribution_from_row 2 2 1 19 0 row_02_02_01_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_19

theorem row_02_02_01_20 : b4RowContribution (![2, 4, 5, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 25] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 25 = 36
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 670 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 25^2 = 670
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_20

theorem weighted_02_02_01_20 : b4RawGapContribution ![2, 2, 1, 20] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 20] = b4GapPatternWeight 2 1 20 * 0 :=
      b4GapContribution_from_row 2 2 1 20 0 row_02_02_01_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_20

theorem row_02_02_01_21 : b4RowContribution (![2, 4, 5, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 5, 26] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 5 + 26 = 37
    decide
  have hzsq : (∑ i, (((![2, 4, 5, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 721 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 5^2 + 26^2 = 721
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_01_21

theorem weighted_02_02_01_21 : b4RawGapContribution ![2, 2, 1, 21] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 1, 21] = b4GapPatternWeight 2 1 21 * 0 :=
      b4GapContribution_from_row 2 2 1 21 0 row_02_02_01_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_01_21

def dvalues_02_02_01 : Fin 22 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 2160, 744, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_02_01

theorem dblock_02_02_01 : b4GapPatternDBlock 2 2 1 = 2904 := by
  calc
    b4GapPatternDBlock 2 2 1 = ∑ d : Fin 22, dvalues_02_02_01 d := by
      apply b4GapDBlock_of_rows 2 2 1 dvalues_02_02_01
      intro d
      fin_cases d
      · exact weighted_02_02_01_00
      · exact weighted_02_02_01_01
      · exact weighted_02_02_01_02
      · exact weighted_02_02_01_03
      · exact weighted_02_02_01_04
      · exact weighted_02_02_01_05
      · exact weighted_02_02_01_06
      · exact weighted_02_02_01_07
      · exact weighted_02_02_01_08
      · exact weighted_02_02_01_09
      · exact weighted_02_02_01_10
      · exact weighted_02_02_01_11
      · exact weighted_02_02_01_12
      · exact weighted_02_02_01_13
      · exact weighted_02_02_01_14
      · exact weighted_02_02_01_15
      · exact weighted_02_02_01_16
      · exact weighted_02_02_01_17
      · exact weighted_02_02_01_18
      · exact weighted_02_02_01_19
      · exact weighted_02_02_01_20
      · exact weighted_02_02_01_21
    _ = 2904 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_02_01

end Paper7MomentGapNumeric
