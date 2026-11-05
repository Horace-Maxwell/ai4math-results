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

theorem row_01_00_04_00 : b4RowContribution (![1, 1, 5, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 5] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 5 = 12
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 52 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 5^2 = 52
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_00

theorem weighted_01_00_04_00 : b4RawGapContribution ![1, 0, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 0] = b4GapPatternWeight 0 4 0 * 0 :=
      b4GapContribution_from_row 1 0 4 0 0 row_01_00_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_00

theorem row_01_00_04_01 : b4RowContribution (![1, 1, 5, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 6] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 6 = 13
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 63 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 6^2 = 63
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_01

theorem weighted_01_00_04_01 : b4RawGapContribution ![1, 0, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 1] = b4GapPatternWeight 0 4 1 * 0 :=
      b4GapContribution_from_row 1 0 4 1 0 row_01_00_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_01

theorem row_01_00_04_02 : b4RowContribution (![1, 1, 5, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 7] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 7 = 14
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 76 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 7^2 = 76
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_02

theorem weighted_01_00_04_02 : b4RawGapContribution ![1, 0, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 2] = b4GapPatternWeight 0 4 2 * 0 :=
      b4GapContribution_from_row 1 0 4 2 0 row_01_00_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_02

theorem row_01_00_04_03 : b4RowContribution (![1, 1, 5, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 8] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 8 = 15
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 91 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 8^2 = 91
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_03

theorem weighted_01_00_04_03 : b4RawGapContribution ![1, 0, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 3] = b4GapPatternWeight 0 4 3 * 0 :=
      b4GapContribution_from_row 1 0 4 3 0 row_01_00_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_03

theorem row_01_00_04_04 : b4RowContribution (![1, 1, 5, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 9] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 9 = 16
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 108 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 9^2 = 108
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_04

theorem weighted_01_00_04_04 : b4RawGapContribution ![1, 0, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 4] = b4GapPatternWeight 0 4 4 * 0 :=
      b4GapContribution_from_row 1 0 4 4 0 row_01_00_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_04

theorem row_01_00_04_05 : b4RowContribution (![1, 1, 5, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 10] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 10 = 17
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 127 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 10^2 = 127
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_05

theorem weighted_01_00_04_05 : b4RawGapContribution ![1, 0, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 5] = b4GapPatternWeight 0 4 5 * 0 :=
      b4GapContribution_from_row 1 0 4 5 0 row_01_00_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_05

theorem row_01_00_04_06 : b4RowContribution (![1, 1, 5, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 11] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 11 = 18
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 148 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 11^2 = 148
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_06

theorem weighted_01_00_04_06 : b4RawGapContribution ![1, 0, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 6] = b4GapPatternWeight 0 4 6 * 0 :=
      b4GapContribution_from_row 1 0 4 6 0 row_01_00_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_06

def layers_01_00_04_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 23, 24, 24, 24, 24, 24, 24, 23, 20, 16, 12, 8, 4]]
#print axioms Paper7MomentGapNumeric.layers_01_00_04_07

theorem cells_01_00_04_07 : QTableValid (![1, 1, 5, 12] : Fin 4 → ℕ) layers_01_00_04_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_04_07

theorem valid_01_00_04_07 :
    SparseRowValid (![1, 1, 5, 12] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_01_00_04_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 5, 12] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 5 + 12 = 19
      decide
    have hzsq : (∑ i, (((![1, 1, 5, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 171 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 5^2 + 12^2 = 171
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_04_07
#print axioms Paper7MomentGapNumeric.valid_01_00_04_07

def qvalues_01_00_04_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_04_07

theorem row_01_00_04_07 : b4RowContribution (![1, 1, 5, 12] : Fin 4 → ℕ) = 24 := by
  calc
    b4RowContribution (![1, 1, 5, 12] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_01_00_04_07) :=
      sparseRow_sound (![1, 1, 5, 12] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_01_00_04_07) valid_01_00_04_07
    _ = 24 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_04_07 Q := by
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
        _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_04_07

theorem weighted_01_00_04_07 : b4RawGapContribution ![1, 0, 4, 7] = 288 := by
  calc
    b4RawGapContribution ![1, 0, 4, 7] = b4GapPatternWeight 0 4 7 * 24 :=
      b4GapContribution_from_row 1 0 4 7 24 row_01_00_04_07
    _ = 288 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_07

theorem row_01_00_04_08 : b4RowContribution (![1, 1, 5, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 13] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 13 = 20
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 196 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 13^2 = 196
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_08

theorem weighted_01_00_04_08 : b4RawGapContribution ![1, 0, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 8] = b4GapPatternWeight 0 4 8 * 0 :=
      b4GapContribution_from_row 1 0 4 8 0 row_01_00_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_08

def layers_01_00_04_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 23, 24, 24, 24, 24, 24, 24, 24, 24, 23, 20, 16, 12]]
#print axioms Paper7MomentGapNumeric.layers_01_00_04_09

theorem cells_01_00_04_09 : QTableValid (![1, 1, 5, 14] : Fin 4 → ℕ) layers_01_00_04_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_04_09

theorem valid_01_00_04_09 :
    SparseRowValid (![1, 1, 5, 14] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_01_00_04_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 5, 14] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 5 + 14 = 21
      decide
    have hzsq : (∑ i, (((![1, 1, 5, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 223 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 5^2 + 14^2 = 223
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_04_09
#print axioms Paper7MomentGapNumeric.valid_01_00_04_09

def qvalues_01_00_04_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_04_09

theorem row_01_00_04_09 : b4RowContribution (![1, 1, 5, 14] : Fin 4 → ℕ) = 48 := by
  calc
    b4RowContribution (![1, 1, 5, 14] : Fin 4 → ℕ) =
        sparseRowValue ({7, 13} : Finset (Fin 19)) (fun _ => layers_01_00_04_09) :=
      sparseRow_sound (![1, 1, 5, 14] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_01_00_04_09) valid_01_00_04_09
    _ = 48 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_04_09 Q := by
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
        _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_04_09

theorem weighted_01_00_04_09 : b4RawGapContribution ![1, 0, 4, 9] = 576 := by
  calc
    b4RawGapContribution ![1, 0, 4, 9] = b4GapPatternWeight 0 4 9 * 48 :=
      b4GapContribution_from_row 1 0 4 9 48 row_01_00_04_09
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_09

theorem row_01_00_04_10 : b4RowContribution (![1, 1, 5, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 15] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 15 = 22
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 252 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 15^2 = 252
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_10

theorem weighted_01_00_04_10 : b4RawGapContribution ![1, 0, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 10] = b4GapPatternWeight 0 4 10 * 0 :=
      b4GapContribution_from_row 1 0 4 10 0 row_01_00_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_10

def layers_01_00_04_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 23, 20]]
#print axioms Paper7MomentGapNumeric.layers_01_00_04_11

theorem cells_01_00_04_11 : QTableValid (![1, 1, 5, 16] : Fin 4 → ℕ) layers_01_00_04_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_04_11

theorem valid_01_00_04_11 :
    SparseRowValid (![1, 1, 5, 16] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_00_04_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 5, 16] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 5 + 16 = 23
      decide
    have hzsq : (∑ i, (((![1, 1, 5, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 283 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 5^2 + 16^2 = 283
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_04_11
#print axioms Paper7MomentGapNumeric.valid_01_00_04_11

def qvalues_01_00_04_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_04_11

theorem row_01_00_04_11 : b4RowContribution (![1, 1, 5, 16] : Fin 4 → ℕ) = 24 := by
  calc
    b4RowContribution (![1, 1, 5, 16] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_00_04_11) :=
      sparseRow_sound (![1, 1, 5, 16] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_00_04_11) valid_01_00_04_11
    _ = 24 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_04_11 Q := by
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
        _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_04_11

theorem weighted_01_00_04_11 : b4RawGapContribution ![1, 0, 4, 11] = 288 := by
  calc
    b4RawGapContribution ![1, 0, 4, 11] = b4GapPatternWeight 0 4 11 * 24 :=
      b4GapContribution_from_row 1 0 4 11 24 row_01_00_04_11
    _ = 288 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_11

theorem row_01_00_04_12 : b4RowContribution (![1, 1, 5, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 17] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 17 = 24
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 316 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 17^2 = 316
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_12

theorem weighted_01_00_04_12 : b4RawGapContribution ![1, 0, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 12] = b4GapPatternWeight 0 4 12 * 0 :=
      b4GapContribution_from_row 1 0 4 12 0 row_01_00_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_12

theorem row_01_00_04_13 : b4RowContribution (![1, 1, 5, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 18] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 18 = 25
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 351 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 18^2 = 351
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_13

theorem weighted_01_00_04_13 : b4RawGapContribution ![1, 0, 4, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 13] = b4GapPatternWeight 0 4 13 * 0 :=
      b4GapContribution_from_row 1 0 4 13 0 row_01_00_04_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_13

theorem row_01_00_04_14 : b4RowContribution (![1, 1, 5, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 19] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 19 = 26
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 388 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 19^2 = 388
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_14

theorem weighted_01_00_04_14 : b4RawGapContribution ![1, 0, 4, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 14] = b4GapPatternWeight 0 4 14 * 0 :=
      b4GapContribution_from_row 1 0 4 14 0 row_01_00_04_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_14

theorem row_01_00_04_15 : b4RowContribution (![1, 1, 5, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 20] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 20 = 27
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 427 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 20^2 = 427
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_15

theorem weighted_01_00_04_15 : b4RawGapContribution ![1, 0, 4, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 15] = b4GapPatternWeight 0 4 15 * 0 :=
      b4GapContribution_from_row 1 0 4 15 0 row_01_00_04_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_15

theorem row_01_00_04_16 : b4RowContribution (![1, 1, 5, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 21] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 21 = 28
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 468 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 21^2 = 468
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_16

theorem weighted_01_00_04_16 : b4RawGapContribution ![1, 0, 4, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 16] = b4GapPatternWeight 0 4 16 * 0 :=
      b4GapContribution_from_row 1 0 4 16 0 row_01_00_04_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_16

def layers_01_00_04_17 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24]]
#print axioms Paper7MomentGapNumeric.layers_01_00_04_17

theorem cells_01_00_04_17 : QTableValid (![1, 1, 5, 22] : Fin 4 → ℕ) layers_01_00_04_17 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_04_17

theorem valid_01_00_04_17 :
    SparseRowValid (![1, 1, 5, 22] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_00_04_17) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 5, 22] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 5 + 22 = 29
      decide
    have hzsq : (∑ i, (((![1, 1, 5, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 511 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 5^2 + 22^2 = 511
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_04_17
#print axioms Paper7MomentGapNumeric.valid_01_00_04_17

def qvalues_01_00_04_17 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_04_17

theorem row_01_00_04_17 : b4RowContribution (![1, 1, 5, 22] : Fin 4 → ℕ) = 24 := by
  calc
    b4RowContribution (![1, 1, 5, 22] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_01_00_04_17) :=
      sparseRow_sound (![1, 1, 5, 22] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_00_04_17) valid_01_00_04_17
    _ = 24 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_04_17 Q := by
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
        _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_04_17

theorem weighted_01_00_04_17 : b4RawGapContribution ![1, 0, 4, 17] = 288 := by
  calc
    b4RawGapContribution ![1, 0, 4, 17] = b4GapPatternWeight 0 4 17 * 24 :=
      b4GapContribution_from_row 1 0 4 17 24 row_01_00_04_17
    _ = 288 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_17

def layers_01_00_04_18 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24]]
#print axioms Paper7MomentGapNumeric.layers_01_00_04_18

theorem cells_01_00_04_18 : QTableValid (![1, 1, 5, 23] : Fin 4 → ℕ) layers_01_00_04_18 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_04_18

theorem valid_01_00_04_18 :
    SparseRowValid (![1, 1, 5, 23] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_00_04_18) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 5, 23] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 5 + 23 = 30
      decide
    have hzsq : (∑ i, (((![1, 1, 5, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 556 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 5^2 + 23^2 = 556
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_04_18
#print axioms Paper7MomentGapNumeric.valid_01_00_04_18

def qvalues_01_00_04_18 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_04_18

theorem row_01_00_04_18 : b4RowContribution (![1, 1, 5, 23] : Fin 4 → ℕ) = 24 := by
  calc
    b4RowContribution (![1, 1, 5, 23] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_01_00_04_18) :=
      sparseRow_sound (![1, 1, 5, 23] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_00_04_18) valid_01_00_04_18
    _ = 24 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_04_18 Q := by
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
        _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_04_18

theorem weighted_01_00_04_18 : b4RawGapContribution ![1, 0, 4, 18] = 288 := by
  calc
    b4RawGapContribution ![1, 0, 4, 18] = b4GapPatternWeight 0 4 18 * 24 :=
      b4GapContribution_from_row 1 0 4 18 24 row_01_00_04_18
    _ = 288 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_18

theorem row_01_00_04_19 : b4RowContribution (![1, 1, 5, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 24] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 24 = 31
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 603 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 24^2 = 603
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_19

theorem weighted_01_00_04_19 : b4RawGapContribution ![1, 0, 4, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 19] = b4GapPatternWeight 0 4 19 * 0 :=
      b4GapContribution_from_row 1 0 4 19 0 row_01_00_04_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_19

theorem row_01_00_04_20 : b4RowContribution (![1, 1, 5, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 25] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 25 = 32
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 652 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 25^2 = 652
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_20

theorem weighted_01_00_04_20 : b4RawGapContribution ![1, 0, 4, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 20] = b4GapPatternWeight 0 4 20 * 0 :=
      b4GapContribution_from_row 1 0 4 20 0 row_01_00_04_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_20

theorem row_01_00_04_21 : b4RowContribution (![1, 1, 5, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 26] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 26 = 33
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 703 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 26^2 = 703
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_21

theorem weighted_01_00_04_21 : b4RawGapContribution ![1, 0, 4, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 21] = b4GapPatternWeight 0 4 21 * 0 :=
      b4GapContribution_from_row 1 0 4 21 0 row_01_00_04_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_21

theorem row_01_00_04_22 : b4RowContribution (![1, 1, 5, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 27] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 27 = 34
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 756 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 27^2 = 756
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_22

theorem weighted_01_00_04_22 : b4RawGapContribution ![1, 0, 4, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 22] = b4GapPatternWeight 0 4 22 * 0 :=
      b4GapContribution_from_row 1 0 4 22 0 row_01_00_04_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_22

theorem row_01_00_04_23 : b4RowContribution (![1, 1, 5, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 28] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 28 = 35
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 811 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 28^2 = 811
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_23

theorem weighted_01_00_04_23 : b4RawGapContribution ![1, 0, 4, 23] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 23] = b4GapPatternWeight 0 4 23 * 0 :=
      b4GapContribution_from_row 1 0 4 23 0 row_01_00_04_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_23

theorem row_01_00_04_24 : b4RowContribution (![1, 1, 5, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 29] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 29 = 36
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 868 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 29^2 = 868
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_24

theorem weighted_01_00_04_24 : b4RawGapContribution ![1, 0, 4, 24] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 24] = b4GapPatternWeight 0 4 24 * 0 :=
      b4GapContribution_from_row 1 0 4 24 0 row_01_00_04_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_24

theorem row_01_00_04_25 : b4RowContribution (![1, 1, 5, 30] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 5, 30] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 5 + 30 = 37
    decide
  have hzsq : (∑ i, (((![1, 1, 5, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 927 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 5^2 + 30^2 = 927
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_04_25

theorem weighted_01_00_04_25 : b4RawGapContribution ![1, 0, 4, 25] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 4, 25] = b4GapPatternWeight 0 4 25 * 0 :=
      b4GapContribution_from_row 1 0 4 25 0 row_01_00_04_25
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_04_25

def dvalues_01_00_04 : Fin 26 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 288, 0, 576, 0, 288, 0, 0, 0, 0, 0, 288, 288, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_00_04

theorem dblock_01_00_04 : b4GapPatternDBlock 1 0 4 = 1728 := by
  calc
    b4GapPatternDBlock 1 0 4 = ∑ d : Fin 26, dvalues_01_00_04 d := by
      apply b4GapDBlock_of_rows 1 0 4 dvalues_01_00_04
      intro d
      fin_cases d
      · exact weighted_01_00_04_00
      · exact weighted_01_00_04_01
      · exact weighted_01_00_04_02
      · exact weighted_01_00_04_03
      · exact weighted_01_00_04_04
      · exact weighted_01_00_04_05
      · exact weighted_01_00_04_06
      · exact weighted_01_00_04_07
      · exact weighted_01_00_04_08
      · exact weighted_01_00_04_09
      · exact weighted_01_00_04_10
      · exact weighted_01_00_04_11
      · exact weighted_01_00_04_12
      · exact weighted_01_00_04_13
      · exact weighted_01_00_04_14
      · exact weighted_01_00_04_15
      · exact weighted_01_00_04_16
      · exact weighted_01_00_04_17
      · exact weighted_01_00_04_18
      · exact weighted_01_00_04_19
      · exact weighted_01_00_04_20
      · exact weighted_01_00_04_21
      · exact weighted_01_00_04_22
      · exact weighted_01_00_04_23
      · exact weighted_01_00_04_24
      · exact weighted_01_00_04_25
    _ = 1728 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_00_04

end Paper7MomentGapNumeric
