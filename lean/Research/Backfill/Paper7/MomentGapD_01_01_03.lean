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

theorem row_01_01_03_00 : b4RowContribution (![1, 2, 5, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 5] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 5 = 13
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 55 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 5^2 = 55
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_00

theorem weighted_01_01_03_00 : b4RawGapContribution ![1, 1, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 0] = b4GapPatternWeight 1 3 0 * 0 :=
      b4GapContribution_from_row 1 1 3 0 0 row_01_01_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_00

theorem row_01_01_03_01 : b4RowContribution (![1, 2, 5, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 6] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 6 = 14
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 66 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 6^2 = 66
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_01

theorem weighted_01_01_03_01 : b4RawGapContribution ![1, 1, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 1] = b4GapPatternWeight 1 3 1 * 0 :=
      b4GapContribution_from_row 1 1 3 1 0 row_01_01_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_01

theorem row_01_01_03_02 : b4RowContribution (![1, 2, 5, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 7] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 7 = 15
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 79 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 7^2 = 79
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_02

theorem weighted_01_01_03_02 : b4RawGapContribution ![1, 1, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 2] = b4GapPatternWeight 1 3 2 * 0 :=
      b4GapContribution_from_row 1 1 3 2 0 row_01_01_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_02

theorem row_01_01_03_03 : b4RowContribution (![1, 2, 5, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 8] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 8 = 16
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 94 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 8^2 = 94
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_03

theorem weighted_01_01_03_03 : b4RawGapContribution ![1, 1, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 3] = b4GapPatternWeight 1 3 3 * 0 :=
      b4GapContribution_from_row 1 1 3 3 0 row_01_01_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_03

theorem row_01_01_03_04 : b4RowContribution (![1, 2, 5, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 9] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 9 = 17
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 111 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 9^2 = 111
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_04

theorem weighted_01_01_03_04 : b4RawGapContribution ![1, 1, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 4] = b4GapPatternWeight 1 3 4 * 0 :=
      b4GapContribution_from_row 1 1 3 4 0 row_01_01_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_04

theorem row_01_01_03_05 : b4RowContribution (![1, 2, 5, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 10] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 10 = 18
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 130 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 10^2 = 130
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_05

theorem weighted_01_01_03_05 : b4RawGapContribution ![1, 1, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 5] = b4GapPatternWeight 1 3 5 * 0 :=
      b4GapContribution_from_row 1 1 3 5 0 row_01_01_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_05

theorem row_01_01_03_06 : b4RowContribution (![1, 2, 5, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 11] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 11 = 19
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 151 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 11^2 = 151
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_06

theorem weighted_01_01_03_06 : b4RawGapContribution ![1, 1, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 6] = b4GapPatternWeight 1 3 6 * 0 :=
      b4GapContribution_from_row 1 1 3 6 0 row_01_01_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_06

def layers_01_01_03_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 27, 32, 35, 36, 36, 36, 36, 36, 35, 32, 27, 21, 15, 9]]
#print axioms Paper7MomentGapNumeric.layers_01_01_03_07

theorem cells_01_01_03_07 : QTableValid (![1, 2, 5, 12] : Fin 4 → ℕ) layers_01_01_03_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_03_07

theorem valid_01_01_03_07 :
    SparseRowValid (![1, 2, 5, 12] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_01_03_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 5, 12] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 5 + 12 = 20
      decide
    have hzsq : (∑ i, (((![1, 2, 5, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 174 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 5^2 + 12^2 = 174
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_03_07
#print axioms Paper7MomentGapNumeric.valid_01_01_03_07

def qvalues_01_01_03_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_03_07

theorem row_01_01_03_07 : b4RowContribution (![1, 2, 5, 12] : Fin 4 → ℕ) = 36 := by
  calc
    b4RowContribution (![1, 2, 5, 12] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_01_03_07) :=
      sparseRow_sound (![1, 2, 5, 12] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_01_03_07) valid_01_01_03_07
    _ = 36 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_03_07 Q := by
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
        _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_03_07

theorem weighted_01_01_03_07 : b4RawGapContribution ![1, 1, 3, 7] = 864 := by
  calc
    b4RawGapContribution ![1, 1, 3, 7] = b4GapPatternWeight 1 3 7 * 36 :=
      b4GapContribution_from_row 1 1 3 7 36 row_01_01_03_07
    _ = 864 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_07

theorem row_01_01_03_08 : b4RowContribution (![1, 2, 5, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 13] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 13 = 21
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 199 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 13^2 = 199
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_08

theorem weighted_01_01_03_08 : b4RawGapContribution ![1, 1, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 8] = b4GapPatternWeight 1 3 8 * 0 :=
      b4GapContribution_from_row 1 1 3 8 0 row_01_01_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_08

def layers_01_01_03_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 27, 32, 35, 36, 36, 36, 36, 36, 36, 36, 35, 32, 27, 21]]
#print axioms Paper7MomentGapNumeric.layers_01_01_03_09

theorem cells_01_01_03_09 : QTableValid (![1, 2, 5, 14] : Fin 4 → ℕ) layers_01_01_03_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_03_09

theorem valid_01_01_03_09 :
    SparseRowValid (![1, 2, 5, 14] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_01_03_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 5, 14] : Fin 4 → ℕ) i) = 22 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 5 + 14 = 22
      decide
    have hzsq : (∑ i, (((![1, 2, 5, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 226 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 5^2 + 14^2 = 226
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_03_09
#print axioms Paper7MomentGapNumeric.valid_01_01_03_09

def qvalues_01_01_03_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_03_09

theorem row_01_01_03_09 : b4RowContribution (![1, 2, 5, 14] : Fin 4 → ℕ) = 36 := by
  calc
    b4RowContribution (![1, 2, 5, 14] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_01_03_09) :=
      sparseRow_sound (![1, 2, 5, 14] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_01_03_09) valid_01_01_03_09
    _ = 36 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_03_09 Q := by
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
        _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_03_09

theorem weighted_01_01_03_09 : b4RawGapContribution ![1, 1, 3, 9] = 864 := by
  calc
    b4RawGapContribution ![1, 1, 3, 9] = b4GapPatternWeight 1 3 9 * 36 :=
      b4GapContribution_from_row 1 1 3 9 36 row_01_01_03_09
    _ = 864 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_09

theorem row_01_01_03_10 : b4RowContribution (![1, 2, 5, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 15] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 15 = 23
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 255 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 15^2 = 255
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_10

theorem weighted_01_01_03_10 : b4RawGapContribution ![1, 1, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 10] = b4GapPatternWeight 1 3 10 * 0 :=
      b4GapContribution_from_row 1 1 3 10 0 row_01_01_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_10

def layers_01_01_03_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 6, 6, 6, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 15, 21, 27, 32, 35, 36, 36, 36, 36, 36, 36, 36, 36, 36, 35, 32]]
#print axioms Paper7MomentGapNumeric.layers_01_01_03_11

theorem cells_01_01_03_11 : QTableValid (![1, 2, 5, 16] : Fin 4 → ℕ) layers_01_01_03_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_01_03_11

theorem valid_01_01_03_11 :
    SparseRowValid (![1, 2, 5, 16] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_01_01_03_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 2, 5, 16] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 1 + 2 + 5 + 16 = 24
      decide
    have hzsq : (∑ i, (((![1, 2, 5, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 286 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 2^2 + 5^2 + 16^2 = 286
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_01_03_11
#print axioms Paper7MomentGapNumeric.valid_01_01_03_11

def qvalues_01_01_03_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_01_03_11

theorem row_01_01_03_11 : b4RowContribution (![1, 2, 5, 16] : Fin 4 → ℕ) = 71 := by
  calc
    b4RowContribution (![1, 2, 5, 16] : Fin 4 → ℕ) =
        sparseRowValue ({7, 13} : Finset (Fin 19)) (fun _ => layers_01_01_03_11) :=
      sparseRow_sound (![1, 2, 5, 16] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_01_01_03_11) valid_01_01_03_11
    _ = 71 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_01_03_11 Q := by
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
        _ = 71 := by decide
#print axioms Paper7MomentGapNumeric.row_01_01_03_11

theorem weighted_01_01_03_11 : b4RawGapContribution ![1, 1, 3, 11] = 1704 := by
  calc
    b4RawGapContribution ![1, 1, 3, 11] = b4GapPatternWeight 1 3 11 * 71 :=
      b4GapContribution_from_row 1 1 3 11 71 row_01_01_03_11
    _ = 1704 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_11

theorem row_01_01_03_12 : b4RowContribution (![1, 2, 5, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 17] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 17 = 25
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 319 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 17^2 = 319
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_12

theorem weighted_01_01_03_12 : b4RawGapContribution ![1, 1, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 12] = b4GapPatternWeight 1 3 12 * 0 :=
      b4GapContribution_from_row 1 1 3 12 0 row_01_01_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_12

theorem row_01_01_03_13 : b4RowContribution (![1, 2, 5, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 18] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 18 = 26
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 354 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 18^2 = 354
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_13

theorem weighted_01_01_03_13 : b4RawGapContribution ![1, 1, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 13] = b4GapPatternWeight 1 3 13 * 0 :=
      b4GapContribution_from_row 1 1 3 13 0 row_01_01_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_13

theorem row_01_01_03_14 : b4RowContribution (![1, 2, 5, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 19] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 19 = 27
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 391 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 19^2 = 391
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_14

theorem weighted_01_01_03_14 : b4RawGapContribution ![1, 1, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 14] = b4GapPatternWeight 1 3 14 * 0 :=
      b4GapContribution_from_row 1 1 3 14 0 row_01_01_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_14

theorem row_01_01_03_15 : b4RowContribution (![1, 2, 5, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 20] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 20 = 28
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 430 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 20^2 = 430
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_15

theorem weighted_01_01_03_15 : b4RawGapContribution ![1, 1, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 15] = b4GapPatternWeight 1 3 15 * 0 :=
      b4GapContribution_from_row 1 1 3 15 0 row_01_01_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_15

theorem row_01_01_03_16 : b4RowContribution (![1, 2, 5, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 21] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 21 = 29
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 471 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 21^2 = 471
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_16

theorem weighted_01_01_03_16 : b4RawGapContribution ![1, 1, 3, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 16] = b4GapPatternWeight 1 3 16 * 0 :=
      b4GapContribution_from_row 1 1 3 16 0 row_01_01_03_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_16

theorem row_01_01_03_17 : b4RowContribution (![1, 2, 5, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 22] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 22 = 30
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 514 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 22^2 = 514
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_17

theorem weighted_01_01_03_17 : b4RawGapContribution ![1, 1, 3, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 17] = b4GapPatternWeight 1 3 17 * 0 :=
      b4GapContribution_from_row 1 1 3 17 0 row_01_01_03_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_17

theorem row_01_01_03_18 : b4RowContribution (![1, 2, 5, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 23] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 23 = 31
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 559 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 23^2 = 559
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_18

theorem weighted_01_01_03_18 : b4RawGapContribution ![1, 1, 3, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 18] = b4GapPatternWeight 1 3 18 * 0 :=
      b4GapContribution_from_row 1 1 3 18 0 row_01_01_03_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_18

theorem row_01_01_03_19 : b4RowContribution (![1, 2, 5, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 24] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 24 = 32
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 606 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 24^2 = 606
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_19

theorem weighted_01_01_03_19 : b4RawGapContribution ![1, 1, 3, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 19] = b4GapPatternWeight 1 3 19 * 0 :=
      b4GapContribution_from_row 1 1 3 19 0 row_01_01_03_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_19

theorem row_01_01_03_20 : b4RowContribution (![1, 2, 5, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 25] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 25 = 33
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 655 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 25^2 = 655
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_20

theorem weighted_01_01_03_20 : b4RawGapContribution ![1, 1, 3, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 20] = b4GapPatternWeight 1 3 20 * 0 :=
      b4GapContribution_from_row 1 1 3 20 0 row_01_01_03_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_20

theorem row_01_01_03_21 : b4RowContribution (![1, 2, 5, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 26] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 26 = 34
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 706 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 26^2 = 706
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_21

theorem weighted_01_01_03_21 : b4RawGapContribution ![1, 1, 3, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 21] = b4GapPatternWeight 1 3 21 * 0 :=
      b4GapContribution_from_row 1 1 3 21 0 row_01_01_03_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_21

theorem row_01_01_03_22 : b4RowContribution (![1, 2, 5, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 27] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 27 = 35
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 759 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 27^2 = 759
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_22

theorem weighted_01_01_03_22 : b4RawGapContribution ![1, 1, 3, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 22] = b4GapPatternWeight 1 3 22 * 0 :=
      b4GapContribution_from_row 1 1 3 22 0 row_01_01_03_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_22

theorem row_01_01_03_23 : b4RowContribution (![1, 2, 5, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 28] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 28 = 36
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 814 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 28^2 = 814
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_23

theorem weighted_01_01_03_23 : b4RawGapContribution ![1, 1, 3, 23] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 23] = b4GapPatternWeight 1 3 23 * 0 :=
      b4GapContribution_from_row 1 1 3 23 0 row_01_01_03_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_23

theorem row_01_01_03_24 : b4RowContribution (![1, 2, 5, 29] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 2, 5, 29] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 2 + 5 + 29 = 37
    decide
  have hzsq : (∑ i, (((![1, 2, 5, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 871 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 2^2 + 5^2 + 29^2 = 871
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_01_03_24

theorem weighted_01_01_03_24 : b4RawGapContribution ![1, 1, 3, 24] = 0 := by
  calc
    b4RawGapContribution ![1, 1, 3, 24] = b4GapPatternWeight 1 3 24 * 0 :=
      b4GapContribution_from_row 1 1 3 24 0 row_01_01_03_24
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_01_03_24

def dvalues_01_01_03 : Fin 25 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 864, 0, 864, 0, 1704, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_01_03

theorem dblock_01_01_03 : b4GapPatternDBlock 1 1 3 = 3432 := by
  calc
    b4GapPatternDBlock 1 1 3 = ∑ d : Fin 25, dvalues_01_01_03 d := by
      apply b4GapDBlock_of_rows 1 1 3 dvalues_01_01_03
      intro d
      fin_cases d
      · exact weighted_01_01_03_00
      · exact weighted_01_01_03_01
      · exact weighted_01_01_03_02
      · exact weighted_01_01_03_03
      · exact weighted_01_01_03_04
      · exact weighted_01_01_03_05
      · exact weighted_01_01_03_06
      · exact weighted_01_01_03_07
      · exact weighted_01_01_03_08
      · exact weighted_01_01_03_09
      · exact weighted_01_01_03_10
      · exact weighted_01_01_03_11
      · exact weighted_01_01_03_12
      · exact weighted_01_01_03_13
      · exact weighted_01_01_03_14
      · exact weighted_01_01_03_15
      · exact weighted_01_01_03_16
      · exact weighted_01_01_03_17
      · exact weighted_01_01_03_18
      · exact weighted_01_01_03_19
      · exact weighted_01_01_03_20
      · exact weighted_01_01_03_21
      · exact weighted_01_01_03_22
      · exact weighted_01_01_03_23
      · exact weighted_01_01_03_24
    _ = 3432 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_01_03

end Paper7MomentGapNumeric
