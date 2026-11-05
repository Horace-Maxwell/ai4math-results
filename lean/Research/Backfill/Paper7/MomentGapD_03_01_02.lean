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

theorem row_03_01_02_00 : b4RowContribution (![3, 4, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 6] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 6 = 19
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 97 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 6^2 = 97
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_00

theorem weighted_03_01_02_00 : b4RawGapContribution ![3, 1, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 0] = b4GapPatternWeight 1 2 0 * 0 :=
      b4GapContribution_from_row 3 1 2 0 0 row_03_01_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_00

theorem row_03_01_02_01 : b4RowContribution (![3, 4, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 7] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 7 = 20
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 110 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 7^2 = 110
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_01

theorem weighted_03_01_02_01 : b4RawGapContribution ![3, 1, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 1] = b4GapPatternWeight 1 2 1 * 0 :=
      b4GapContribution_from_row 3 1 2 1 0 row_03_01_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_01

theorem row_03_01_02_02 : b4RowContribution (![3, 4, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 8] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 8 = 21
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 125 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 8^2 = 125
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_02

theorem weighted_03_01_02_02 : b4RawGapContribution ![3, 1, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 2] = b4GapPatternWeight 1 2 2 * 0 :=
      b4GapContribution_from_row 3 1 2 2 0 row_03_01_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_02

theorem row_03_01_02_03 : b4RowContribution (![3, 4, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 9] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 9 = 22
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 142 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 9^2 = 142
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_03

theorem weighted_03_01_02_03 : b4RawGapContribution ![3, 1, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 3] = b4GapPatternWeight 1 2 3 * 0 :=
      b4GapContribution_from_row 3 1 2 3 0 row_03_01_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_03

theorem row_03_01_02_04 : b4RowContribution (![3, 4, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 10] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 10 = 23
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 161 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 10^2 = 161
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_04

theorem weighted_03_01_02_04 : b4RawGapContribution ![3, 1, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 4] = b4GapPatternWeight 1 2 4 * 0 :=
      b4GapContribution_from_row 3 1 2 4 0 row_03_01_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_04

theorem row_03_01_02_05 : b4RowContribution (![3, 4, 6, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 11] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 11 = 24
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 182 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 11^2 = 182
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_05

theorem weighted_03_01_02_05 : b4RawGapContribution ![3, 1, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 5] = b4GapPatternWeight 1 2 5 * 0 :=
      b4GapContribution_from_row 3 1 2 5 0 row_03_01_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_05

theorem row_03_01_02_06 : b4RowContribution (![3, 4, 6, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 12] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 12 = 25
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 205 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 12^2 = 205
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_06

theorem weighted_03_01_02_06 : b4RawGapContribution ![3, 1, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 6] = b4GapPatternWeight 1 2 6 * 0 :=
      b4GapContribution_from_row 3 1 2 6 0 row_03_01_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_06

def layers_03_01_02_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 17, 19, 19, 17, 14, 10, 6, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 34, 51, 70, 89, 106, 120, 130, 136, 139, 140, 139, 136, 130, 120, 106]]
#print axioms Paper7MomentGapNumeric.layers_03_01_02_07

theorem cells_03_01_02_07 : QTableValid (![3, 4, 6, 13] : Fin 4 → ℕ) layers_03_01_02_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_01_02_07

theorem valid_03_01_02_07 :
    SparseRowValid (![3, 4, 6, 13] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_03_01_02_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 4, 6, 13] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 3 + 4 + 6 + 13 = 26
      decide
    have hzsq : (∑ i, (((![3, 4, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 230 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 4^2 + 6^2 + 13^2 = 230
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_01_02_07
#print axioms Paper7MomentGapNumeric.valid_03_01_02_07

def qvalues_03_01_02_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_01_02_07

theorem row_03_01_02_07 : b4RowContribution (![3, 4, 6, 13] : Fin 4 → ℕ) = 106 := by
  calc
    b4RowContribution (![3, 4, 6, 13] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_03_01_02_07) :=
      sparseRow_sound (![3, 4, 6, 13] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_03_01_02_07) valid_03_01_02_07
    _ = 106 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_01_02_07 Q := by
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
        _ = 106 := by decide
#print axioms Paper7MomentGapNumeric.row_03_01_02_07

theorem weighted_03_01_02_07 : b4RawGapContribution ![3, 1, 2, 7] = 2544 := by
  calc
    b4RawGapContribution ![3, 1, 2, 7] = b4GapPatternWeight 1 2 7 * 106 :=
      b4GapContribution_from_row 3 1 2 7 106 row_03_01_02_07
    _ = 2544 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_07

theorem row_03_01_02_08 : b4RowContribution (![3, 4, 6, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 14] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 14 = 27
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 257 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 14^2 = 257
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_08

theorem weighted_03_01_02_08 : b4RawGapContribution ![3, 1, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 8] = b4GapPatternWeight 1 2 8 * 0 :=
      b4GapContribution_from_row 3 1 2 8 0 row_03_01_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_08

def layers_03_01_02_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 17, 19, 19, 17, 14, 10, 6, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 34, 51, 70, 89, 106, 120, 130, 136, 139, 140, 140, 140, 139, 136, 130]]
#print axioms Paper7MomentGapNumeric.layers_03_01_02_09

theorem cells_03_01_02_09 : QTableValid (![3, 4, 6, 15] : Fin 4 → ℕ) layers_03_01_02_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_01_02_09

theorem valid_03_01_02_09 :
    SparseRowValid (![3, 4, 6, 15] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_03_01_02_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 4, 6, 15] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 3 + 4 + 6 + 15 = 28
      decide
    have hzsq : (∑ i, (((![3, 4, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 286 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 4^2 + 6^2 + 15^2 = 286
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_01_02_09
#print axioms Paper7MomentGapNumeric.valid_03_01_02_09

def qvalues_03_01_02_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 89, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_01_02_09

theorem row_03_01_02_09 : b4RowContribution (![3, 4, 6, 15] : Fin 4 → ℕ) = 89 := by
  calc
    b4RowContribution (![3, 4, 6, 15] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_03_01_02_09) :=
      sparseRow_sound (![3, 4, 6, 15] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_03_01_02_09) valid_03_01_02_09
    _ = 89 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_01_02_09 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 89 := by decide
#print axioms Paper7MomentGapNumeric.row_03_01_02_09

theorem weighted_03_01_02_09 : b4RawGapContribution ![3, 1, 2, 9] = 2136 := by
  calc
    b4RawGapContribution ![3, 1, 2, 9] = b4GapPatternWeight 1 2 9 * 89 :=
      b4GapContribution_from_row 3 1 2 9 89 row_03_01_02_09
    _ = 2136 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_09

theorem row_03_01_02_10 : b4RowContribution (![3, 4, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 16 = 29
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 317 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 16^2 = 317
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_10

theorem weighted_03_01_02_10 : b4RawGapContribution ![3, 1, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 10] = b4GapPatternWeight 1 2 10 * 0 :=
      b4GapContribution_from_row 3 1 2 10 0 row_03_01_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_10

theorem row_03_01_02_11 : b4RowContribution (![3, 4, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 17 = 30
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 350 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 17^2 = 350
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_11

theorem weighted_03_01_02_11 : b4RawGapContribution ![3, 1, 2, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 11] = b4GapPatternWeight 1 2 11 * 0 :=
      b4GapContribution_from_row 3 1 2 11 0 row_03_01_02_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_11

theorem row_03_01_02_12 : b4RowContribution (![3, 4, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 18 = 31
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 385 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 18^2 = 385
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_12

theorem weighted_03_01_02_12 : b4RawGapContribution ![3, 1, 2, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 12] = b4GapPatternWeight 1 2 12 * 0 :=
      b4GapContribution_from_row 3 1 2 12 0 row_03_01_02_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_12

theorem row_03_01_02_13 : b4RowContribution (![3, 4, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 19 = 32
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 422 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 19^2 = 422
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_13

theorem weighted_03_01_02_13 : b4RawGapContribution ![3, 1, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 13] = b4GapPatternWeight 1 2 13 * 0 :=
      b4GapContribution_from_row 3 1 2 13 0 row_03_01_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_13

theorem row_03_01_02_14 : b4RowContribution (![3, 4, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 20 = 33
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 461 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 20^2 = 461
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_14

theorem weighted_03_01_02_14 : b4RawGapContribution ![3, 1, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 14] = b4GapPatternWeight 1 2 14 * 0 :=
      b4GapContribution_from_row 3 1 2 14 0 row_03_01_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_14

theorem row_03_01_02_15 : b4RowContribution (![3, 4, 6, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 21] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 21 = 34
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 502 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 21^2 = 502
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_15

theorem weighted_03_01_02_15 : b4RawGapContribution ![3, 1, 2, 15] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 15] = b4GapPatternWeight 1 2 15 * 0 :=
      b4GapContribution_from_row 3 1 2 15 0 row_03_01_02_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_15

theorem row_03_01_02_16 : b4RowContribution (![3, 4, 6, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 22 = 35
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 545 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 22^2 = 545
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_16

theorem weighted_03_01_02_16 : b4RawGapContribution ![3, 1, 2, 16] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 16] = b4GapPatternWeight 1 2 16 * 0 :=
      b4GapContribution_from_row 3 1 2 16 0 row_03_01_02_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_16

theorem row_03_01_02_17 : b4RowContribution (![3, 4, 6, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 23 = 36
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 590 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 23^2 = 590
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_17

theorem weighted_03_01_02_17 : b4RawGapContribution ![3, 1, 2, 17] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 17] = b4GapPatternWeight 1 2 17 * 0 :=
      b4GapContribution_from_row 3 1 2 17 0 row_03_01_02_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_17

theorem row_03_01_02_18 : b4RowContribution (![3, 4, 6, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 4, 6, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 4 + 6 + 24 = 37
    decide
  have hzsq : (∑ i, (((![3, 4, 6, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 637 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 4^2 + 6^2 + 24^2 = 637
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_01_02_18

theorem weighted_03_01_02_18 : b4RawGapContribution ![3, 1, 2, 18] = 0 := by
  calc
    b4RawGapContribution ![3, 1, 2, 18] = b4GapPatternWeight 1 2 18 * 0 :=
      b4GapContribution_from_row 3 1 2 18 0 row_03_01_02_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_01_02_18

def dvalues_03_01_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 2544, 0, 2136, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_01_02

theorem dblock_03_01_02 : b4GapPatternDBlock 3 1 2 = 4680 := by
  calc
    b4GapPatternDBlock 3 1 2 = ∑ d : Fin 19, dvalues_03_01_02 d := by
      apply b4GapDBlock_of_rows 3 1 2 dvalues_03_01_02
      intro d
      fin_cases d
      · exact weighted_03_01_02_00
      · exact weighted_03_01_02_01
      · exact weighted_03_01_02_02
      · exact weighted_03_01_02_03
      · exact weighted_03_01_02_04
      · exact weighted_03_01_02_05
      · exact weighted_03_01_02_06
      · exact weighted_03_01_02_07
      · exact weighted_03_01_02_08
      · exact weighted_03_01_02_09
      · exact weighted_03_01_02_10
      · exact weighted_03_01_02_11
      · exact weighted_03_01_02_12
      · exact weighted_03_01_02_13
      · exact weighted_03_01_02_14
      · exact weighted_03_01_02_15
      · exact weighted_03_01_02_16
      · exact weighted_03_01_02_17
      · exact weighted_03_01_02_18
    _ = 4680 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_01_02

end Paper7MomentGapNumeric
