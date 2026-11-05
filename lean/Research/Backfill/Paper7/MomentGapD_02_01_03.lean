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

theorem row_02_01_03_00 : b4RowContribution (![2, 3, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 6] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 6 = 17
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 85 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 6^2 = 85
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_00

theorem weighted_02_01_03_00 : b4RawGapContribution ![2, 1, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 0] = b4GapPatternWeight 1 3 0 * 0 :=
      b4GapContribution_from_row 2 1 3 0 0 row_02_01_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_00

theorem row_02_01_03_01 : b4RowContribution (![2, 3, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 7] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 7 = 18
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 98 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 7^2 = 98
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_01

theorem weighted_02_01_03_01 : b4RawGapContribution ![2, 1, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 1] = b4GapPatternWeight 1 3 1 * 0 :=
      b4GapContribution_from_row 2 1 3 1 0 row_02_01_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_01

theorem row_02_01_03_02 : b4RowContribution (![2, 3, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 8] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 8 = 19
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 113 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 8^2 = 113
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_02

theorem weighted_02_01_03_02 : b4RawGapContribution ![2, 1, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 2] = b4GapPatternWeight 1 3 2 * 0 :=
      b4GapContribution_from_row 2 1 3 2 0 row_02_01_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_02

theorem row_02_01_03_03 : b4RowContribution (![2, 3, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 9] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 9 = 20
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 130 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 9^2 = 130
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_03

theorem weighted_02_01_03_03 : b4RawGapContribution ![2, 1, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 3] = b4GapPatternWeight 1 3 3 * 0 :=
      b4GapContribution_from_row 2 1 3 3 0 row_02_01_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_03

theorem row_02_01_03_04 : b4RowContribution (![2, 3, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 10] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 10 = 21
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 149 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 10^2 = 149
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_04

theorem weighted_02_01_03_04 : b4RawGapContribution ![2, 1, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 4] = b4GapPatternWeight 1 3 4 * 0 :=
      b4GapContribution_from_row 2 1 3 4 0 row_02_01_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_04

theorem row_02_01_03_05 : b4RowContribution (![2, 3, 6, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 11] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 11 = 22
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 170 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 11^2 = 170
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_05

theorem weighted_02_01_03_05 : b4RawGapContribution ![2, 1, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 5] = b4GapPatternWeight 1 3 5 * 0 :=
      b4GapContribution_from_row 2 1 3 5 0 row_02_01_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_05

theorem row_02_01_03_06 : b4RowContribution (![2, 3, 6, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 12] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 12 = 23
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 193 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 12^2 = 193
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_06

theorem weighted_02_01_03_06 : b4RawGapContribution ![2, 1, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 6] = b4GapPatternWeight 1 3 6 * 0 :=
      b4GapContribution_from_row 2 1 3 6 0 row_02_01_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_06

def layers_02_01_03_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 11, 12, 12, 11, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 30, 42, 54, 65, 74, 80, 83, 84, 84, 84, 83, 80, 74, 65, 54]]
#print axioms Paper7MomentGapNumeric.layers_02_01_03_07

theorem cells_02_01_03_07 : QTableValid (![2, 3, 6, 13] : Fin 4 → ℕ) layers_02_01_03_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_03_07

theorem valid_02_01_03_07 :
    SparseRowValid (![2, 3, 6, 13] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_02_01_03_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 6, 13] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 6 + 13 = 24
      decide
    have hzsq : (∑ i, (((![2, 3, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 218 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 6^2 + 13^2 = 218
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_03_07
#print axioms Paper7MomentGapNumeric.valid_02_01_03_07

def qvalues_02_01_03_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_03_07

theorem row_02_01_03_07 : b4RowContribution (![2, 3, 6, 13] : Fin 4 → ℕ) = 84 := by
  calc
    b4RowContribution (![2, 3, 6, 13] : Fin 4 → ℕ) =
        sparseRowValue ({11} : Finset (Fin 19)) (fun _ => layers_02_01_03_07) :=
      sparseRow_sound (![2, 3, 6, 13] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_02_01_03_07) valid_02_01_03_07
    _ = 84 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_03_07 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 84 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_03_07

theorem weighted_02_01_03_07 : b4RawGapContribution ![2, 1, 3, 7] = 2016 := by
  calc
    b4RawGapContribution ![2, 1, 3, 7] = b4GapPatternWeight 1 3 7 * 84 :=
      b4GapContribution_from_row 2 1 3 7 84 row_02_01_03_07
    _ = 2016 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_07

theorem row_02_01_03_08 : b4RowContribution (![2, 3, 6, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 14] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 14 = 25
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 245 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 14^2 = 245
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_08

theorem weighted_02_01_03_08 : b4RawGapContribution ![2, 1, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 8] = b4GapPatternWeight 1 3 8 * 0 :=
      b4GapContribution_from_row 2 1 3 8 0 row_02_01_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_08

def layers_02_01_03_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 11, 12, 12, 11, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 30, 42, 54, 65, 74, 80, 83, 84, 84, 84, 84, 84, 83, 80, 74]]
#print axioms Paper7MomentGapNumeric.layers_02_01_03_09

theorem cells_02_01_03_09 : QTableValid (![2, 3, 6, 15] : Fin 4 → ℕ) layers_02_01_03_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_01_03_09

theorem valid_02_01_03_09 :
    SparseRowValid (![2, 3, 6, 15] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_02_01_03_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 3, 6, 15] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 2 + 3 + 6 + 15 = 26
      decide
    have hzsq : (∑ i, (((![2, 3, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 274 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 3^2 + 6^2 + 15^2 = 274
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_01_03_09
#print axioms Paper7MomentGapNumeric.valid_02_01_03_09

def qvalues_02_01_03_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_01_03_09

theorem row_02_01_03_09 : b4RowContribution (![2, 3, 6, 15] : Fin 4 → ℕ) = 83 := by
  calc
    b4RowContribution (![2, 3, 6, 15] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_02_01_03_09) :=
      sparseRow_sound (![2, 3, 6, 15] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_02_01_03_09) valid_02_01_03_09
    _ = 83 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_01_03_09 Q := by
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
        _ = 83 := by decide
#print axioms Paper7MomentGapNumeric.row_02_01_03_09

theorem weighted_02_01_03_09 : b4RawGapContribution ![2, 1, 3, 9] = 1992 := by
  calc
    b4RawGapContribution ![2, 1, 3, 9] = b4GapPatternWeight 1 3 9 * 83 :=
      b4GapContribution_from_row 2 1 3 9 83 row_02_01_03_09
    _ = 1992 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_09

theorem row_02_01_03_10 : b4RowContribution (![2, 3, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 16] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 16 = 27
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 305 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 16^2 = 305
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_10

theorem weighted_02_01_03_10 : b4RawGapContribution ![2, 1, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 10] = b4GapPatternWeight 1 3 10 * 0 :=
      b4GapContribution_from_row 2 1 3 10 0 row_02_01_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_10

theorem row_02_01_03_11 : b4RowContribution (![2, 3, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 17] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 17 = 28
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 338 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 17^2 = 338
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_11

theorem weighted_02_01_03_11 : b4RawGapContribution ![2, 1, 3, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 11] = b4GapPatternWeight 1 3 11 * 0 :=
      b4GapContribution_from_row 2 1 3 11 0 row_02_01_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_11

theorem row_02_01_03_12 : b4RowContribution (![2, 3, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 18] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 18 = 29
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 373 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 18^2 = 373
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_12

theorem weighted_02_01_03_12 : b4RawGapContribution ![2, 1, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 12] = b4GapPatternWeight 1 3 12 * 0 :=
      b4GapContribution_from_row 2 1 3 12 0 row_02_01_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_12

theorem row_02_01_03_13 : b4RowContribution (![2, 3, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 19] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 19 = 30
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 410 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 19^2 = 410
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_13

theorem weighted_02_01_03_13 : b4RawGapContribution ![2, 1, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 13] = b4GapPatternWeight 1 3 13 * 0 :=
      b4GapContribution_from_row 2 1 3 13 0 row_02_01_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_13

theorem row_02_01_03_14 : b4RowContribution (![2, 3, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 20] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 20 = 31
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 449 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 20^2 = 449
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_14

theorem weighted_02_01_03_14 : b4RawGapContribution ![2, 1, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 14] = b4GapPatternWeight 1 3 14 * 0 :=
      b4GapContribution_from_row 2 1 3 14 0 row_02_01_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_14

theorem row_02_01_03_15 : b4RowContribution (![2, 3, 6, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 21] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 21 = 32
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 490 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 21^2 = 490
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_15

theorem weighted_02_01_03_15 : b4RawGapContribution ![2, 1, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 15] = b4GapPatternWeight 1 3 15 * 0 :=
      b4GapContribution_from_row 2 1 3 15 0 row_02_01_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_15

theorem row_02_01_03_16 : b4RowContribution (![2, 3, 6, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 22] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 22 = 33
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 533 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 22^2 = 533
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_16

theorem weighted_02_01_03_16 : b4RawGapContribution ![2, 1, 3, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 16] = b4GapPatternWeight 1 3 16 * 0 :=
      b4GapContribution_from_row 2 1 3 16 0 row_02_01_03_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_16

theorem row_02_01_03_17 : b4RowContribution (![2, 3, 6, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 23] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 23 = 34
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 578 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 23^2 = 578
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_17

theorem weighted_02_01_03_17 : b4RawGapContribution ![2, 1, 3, 17] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 17] = b4GapPatternWeight 1 3 17 * 0 :=
      b4GapContribution_from_row 2 1 3 17 0 row_02_01_03_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_17

theorem row_02_01_03_18 : b4RowContribution (![2, 3, 6, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 24] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 24 = 35
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 625 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 24^2 = 625
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_18

theorem weighted_02_01_03_18 : b4RawGapContribution ![2, 1, 3, 18] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 18] = b4GapPatternWeight 1 3 18 * 0 :=
      b4GapContribution_from_row 2 1 3 18 0 row_02_01_03_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_18

theorem row_02_01_03_19 : b4RowContribution (![2, 3, 6, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 25] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 25 = 36
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 674 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 25^2 = 674
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_19

theorem weighted_02_01_03_19 : b4RawGapContribution ![2, 1, 3, 19] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 19] = b4GapPatternWeight 1 3 19 * 0 :=
      b4GapContribution_from_row 2 1 3 19 0 row_02_01_03_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_19

theorem row_02_01_03_20 : b4RowContribution (![2, 3, 6, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 3, 6, 26] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 3 + 6 + 26 = 37
    decide
  have hzsq : (∑ i, (((![2, 3, 6, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 725 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 3^2 + 6^2 + 26^2 = 725
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_01_03_20

theorem weighted_02_01_03_20 : b4RawGapContribution ![2, 1, 3, 20] = 0 := by
  calc
    b4RawGapContribution ![2, 1, 3, 20] = b4GapPatternWeight 1 3 20 * 0 :=
      b4GapContribution_from_row 2 1 3 20 0 row_02_01_03_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_01_03_20

def dvalues_02_01_03 : Fin 21 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 2016, 0, 1992, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_01_03

theorem dblock_02_01_03 : b4GapPatternDBlock 2 1 3 = 4008 := by
  calc
    b4GapPatternDBlock 2 1 3 = ∑ d : Fin 21, dvalues_02_01_03 d := by
      apply b4GapDBlock_of_rows 2 1 3 dvalues_02_01_03
      intro d
      fin_cases d
      · exact weighted_02_01_03_00
      · exact weighted_02_01_03_01
      · exact weighted_02_01_03_02
      · exact weighted_02_01_03_03
      · exact weighted_02_01_03_04
      · exact weighted_02_01_03_05
      · exact weighted_02_01_03_06
      · exact weighted_02_01_03_07
      · exact weighted_02_01_03_08
      · exact weighted_02_01_03_09
      · exact weighted_02_01_03_10
      · exact weighted_02_01_03_11
      · exact weighted_02_01_03_12
      · exact weighted_02_01_03_13
      · exact weighted_02_01_03_14
      · exact weighted_02_01_03_15
      · exact weighted_02_01_03_16
      · exact weighted_02_01_03_17
      · exact weighted_02_01_03_18
      · exact weighted_02_01_03_19
      · exact weighted_02_01_03_20
    _ = 4008 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_01_03

end Paper7MomentGapNumeric
