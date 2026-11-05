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

theorem row_01_02_02_00 : b4RowContribution (![1, 3, 5, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 5] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 5 = 14
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 60 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 5^2 = 60
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_00

theorem weighted_01_02_02_00 : b4RawGapContribution ![1, 2, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 0] = b4GapPatternWeight 2 2 0 * 0 :=
      b4GapContribution_from_row 1 2 2 0 0 row_01_02_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_00

theorem row_01_02_02_01 : b4RowContribution (![1, 3, 5, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 6] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 6 = 15
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 71 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 6^2 = 71
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_01

theorem weighted_01_02_02_01 : b4RawGapContribution ![1, 2, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 1] = b4GapPatternWeight 2 2 1 * 0 :=
      b4GapContribution_from_row 1 2 2 1 0 row_01_02_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_01

theorem row_01_02_02_02 : b4RowContribution (![1, 3, 5, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 7] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 7 = 16
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 84 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 7^2 = 84
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_02

theorem weighted_01_02_02_02 : b4RawGapContribution ![1, 2, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 2] = b4GapPatternWeight 2 2 2 * 0 :=
      b4GapContribution_from_row 1 2 2 2 0 row_01_02_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_02

theorem row_01_02_02_03 : b4RowContribution (![1, 3, 5, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 8] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 8 = 17
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 99 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 8^2 = 99
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_03

theorem weighted_01_02_02_03 : b4RawGapContribution ![1, 2, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 3] = b4GapPatternWeight 2 2 3 * 0 :=
      b4GapContribution_from_row 1 2 2 3 0 row_01_02_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_03

theorem row_01_02_02_04 : b4RowContribution (![1, 3, 5, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 9] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 9 = 18
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 116 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 9^2 = 116
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_04

theorem weighted_01_02_02_04 : b4RawGapContribution ![1, 2, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 4] = b4GapPatternWeight 2 2 4 * 0 :=
      b4GapContribution_from_row 1 2 2 4 0 row_01_02_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_04

theorem row_01_02_02_05 : b4RowContribution (![1, 3, 5, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 10] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 10 = 19
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 135 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 10^2 = 135
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_05

theorem weighted_01_02_02_05 : b4RawGapContribution ![1, 2, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 5] = b4GapPatternWeight 2 2 5 * 0 :=
      b4GapContribution_from_row 1 2 2 5 0 row_01_02_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_05

theorem row_01_02_02_06 : b4RowContribution (![1, 3, 5, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 11] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 11 = 20
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 156 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 11^2 = 156
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_06

theorem weighted_01_02_02_06 : b4RawGapContribution ![1, 2, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 6] = b4GapPatternWeight 2 2 6 * 0 :=
      b4GapContribution_from_row 1 2 2 6 0 row_01_02_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_06

theorem row_01_02_02_07 : b4RowContribution (![1, 3, 5, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 12] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 12 = 21
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 179 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 12^2 = 179
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_07

theorem weighted_01_02_02_07 : b4RawGapContribution ![1, 2, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 7] = b4GapPatternWeight 2 2 7 * 0 :=
      b4GapContribution_from_row 1 2 2 7 0 row_01_02_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_07

theorem row_01_02_02_08 : b4RowContribution (![1, 3, 5, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 13] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 13 = 22
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 204 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 13^2 = 204
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_08

theorem weighted_01_02_02_08 : b4RawGapContribution ![1, 2, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 8] = b4GapPatternWeight 2 2 8 * 0 :=
      b4GapContribution_from_row 1 2 2 8 0 row_01_02_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_08

def layers_01_02_02_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 8, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 32, 39, 44, 47, 48, 48, 48, 48, 48, 48, 47, 44, 39, 32]]
#print axioms Paper7MomentGapNumeric.layers_01_02_02_09

theorem cells_01_02_02_09 : QTableValid (![1, 3, 5, 14] : Fin 4 → ℕ) layers_01_02_02_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_02_09

theorem valid_01_02_02_09 :
    SparseRowValid (![1, 3, 5, 14] : Fin 4 → ℕ) ({0, 6, 12} : Finset (Fin 19)) (fun _ => layers_01_02_02_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 5, 14] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 5 + 14 = 23
      decide
    have hzsq : (∑ i, (((![1, 3, 5, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 231 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 5^2 + 14^2 = 231
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_02_09
#print axioms Paper7MomentGapNumeric.valid_01_02_02_09

def qvalues_01_02_02_09 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_02_09

theorem row_01_02_02_09 : b4RowContribution (![1, 3, 5, 14] : Fin 4 → ℕ) = 88 := by
  calc
    b4RowContribution (![1, 3, 5, 14] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6, 12} : Finset (Fin 19)) (fun _ => layers_01_02_02_09) :=
      sparseRow_sound (![1, 3, 5, 14] : Fin 4 → ℕ) ({0, 6, 12} : Finset (Fin 19)) (fun _ => layers_01_02_02_09) valid_01_02_02_09
    _ = 88 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_02_09 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 88 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_02_09

theorem weighted_01_02_02_09 : b4RawGapContribution ![1, 2, 2, 9] = 2112 := by
  calc
    b4RawGapContribution ![1, 2, 2, 9] = b4GapPatternWeight 2 2 9 * 88 :=
      b4GapContribution_from_row 1 2 2 9 88 row_01_02_02_09
    _ = 2112 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_09

theorem row_01_02_02_10 : b4RowContribution (![1, 3, 5, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 15] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 15 = 24
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 260 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 15^2 = 260
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_10

theorem weighted_01_02_02_10 : b4RawGapContribution ![1, 2, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 10] = b4GapPatternWeight 2 2 10 * 0 :=
      b4GapContribution_from_row 1 2 2 10 0 row_01_02_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_10

def layers_01_02_02_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 8, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 32, 39, 44, 47, 48, 48, 48, 48, 48, 48, 48, 48, 47, 44]]
#print axioms Paper7MomentGapNumeric.layers_01_02_02_11

theorem cells_01_02_02_11 : QTableValid (![1, 3, 5, 16] : Fin 4 → ℕ) layers_01_02_02_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_02_11

theorem valid_01_02_02_11 :
    SparseRowValid (![1, 3, 5, 16] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_02_02_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 5, 16] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 5 + 16 = 25
      decide
    have hzsq : (∑ i, (((![1, 3, 5, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 291 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 5^2 + 16^2 = 291
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_02_11
#print axioms Paper7MomentGapNumeric.valid_01_02_02_11

def qvalues_01_02_02_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_02_11

theorem row_01_02_02_11 : b4RowContribution (![1, 3, 5, 16] : Fin 4 → ℕ) = 48 := by
  calc
    b4RowContribution (![1, 3, 5, 16] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_02_02_11) :=
      sparseRow_sound (![1, 3, 5, 16] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_02_02_11) valid_01_02_02_11
    _ = 48 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_02_11 Q := by
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
        _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_02_11

theorem weighted_01_02_02_11 : b4RawGapContribution ![1, 2, 2, 11] = 1152 := by
  calc
    b4RawGapContribution ![1, 2, 2, 11] = b4GapPatternWeight 2 2 11 * 48 :=
      b4GapContribution_from_row 1 2 2 11 48 row_01_02_02_11
    _ = 1152 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_11

theorem row_01_02_02_12 : b4RowContribution (![1, 3, 5, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 17] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 17 = 26
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 324 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 17^2 = 324
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_12

theorem weighted_01_02_02_12 : b4RawGapContribution ![1, 2, 2, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 12] = b4GapPatternWeight 2 2 12 * 0 :=
      b4GapContribution_from_row 1 2 2 12 0 row_01_02_02_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_12

theorem row_01_02_02_13 : b4RowContribution (![1, 3, 5, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 18] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 18 = 27
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 359 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 18^2 = 359
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_13

theorem weighted_01_02_02_13 : b4RawGapContribution ![1, 2, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 13] = b4GapPatternWeight 2 2 13 * 0 :=
      b4GapContribution_from_row 1 2 2 13 0 row_01_02_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_13

theorem row_01_02_02_14 : b4RowContribution (![1, 3, 5, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 19] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 19 = 28
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 396 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 19^2 = 396
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_14

theorem weighted_01_02_02_14 : b4RawGapContribution ![1, 2, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 14] = b4GapPatternWeight 2 2 14 * 0 :=
      b4GapContribution_from_row 1 2 2 14 0 row_01_02_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_14

theorem row_01_02_02_15 : b4RowContribution (![1, 3, 5, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 20] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 20 = 29
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 435 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 20^2 = 435
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_15

theorem weighted_01_02_02_15 : b4RawGapContribution ![1, 2, 2, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 15] = b4GapPatternWeight 2 2 15 * 0 :=
      b4GapContribution_from_row 1 2 2 15 0 row_01_02_02_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_15

theorem row_01_02_02_16 : b4RowContribution (![1, 3, 5, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 21] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 21 = 30
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 476 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 21^2 = 476
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_16

theorem weighted_01_02_02_16 : b4RawGapContribution ![1, 2, 2, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 16] = b4GapPatternWeight 2 2 16 * 0 :=
      b4GapContribution_from_row 1 2 2 16 0 row_01_02_02_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_16

def layers_01_02_02_17 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 8, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 32, 39, 44, 47, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48]]
#print axioms Paper7MomentGapNumeric.layers_01_02_02_17

theorem cells_01_02_02_17 : QTableValid (![1, 3, 5, 22] : Fin 4 → ℕ) layers_01_02_02_17 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_02_17

theorem valid_01_02_02_17 :
    SparseRowValid (![1, 3, 5, 22] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_01_02_02_17) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 5, 22] : Fin 4 → ℕ) i) = 31 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 5 + 22 = 31
      decide
    have hzsq : (∑ i, (((![1, 3, 5, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 519 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 5^2 + 22^2 = 519
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_02_17
#print axioms Paper7MomentGapNumeric.valid_01_02_02_17

def qvalues_01_02_02_17 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_02_17

theorem row_01_02_02_17 : b4RowContribution (![1, 3, 5, 22] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![1, 3, 5, 22] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_01_02_02_17) :=
      sparseRow_sound (![1, 3, 5, 22] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_01_02_02_17) valid_01_02_02_17
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_02_17 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_02_02_17

theorem weighted_01_02_02_17 : b4RawGapContribution ![1, 2, 2, 17] = 24 := by
  calc
    b4RawGapContribution ![1, 2, 2, 17] = b4GapPatternWeight 2 2 17 * 1 :=
      b4GapContribution_from_row 1 2 2 17 1 row_01_02_02_17
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_17

def layers_01_02_02_18 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 8, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 24, 32, 39, 44, 47, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48]]
#print axioms Paper7MomentGapNumeric.layers_01_02_02_18

theorem cells_01_02_02_18 : QTableValid (![1, 3, 5, 23] : Fin 4 → ℕ) layers_01_02_02_18 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_02_18

theorem valid_01_02_02_18 :
    SparseRowValid (![1, 3, 5, 23] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_01_02_02_18) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 5, 23] : Fin 4 → ℕ) i) = 32 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 5 + 23 = 32
      decide
    have hzsq : (∑ i, (((![1, 3, 5, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 564 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 5^2 + 23^2 = 564
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_02_18
#print axioms Paper7MomentGapNumeric.valid_01_02_02_18

def qvalues_01_02_02_18 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_02_18

theorem row_01_02_02_18 : b4RowContribution (![1, 3, 5, 23] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![1, 3, 5, 23] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_01_02_02_18) :=
      sparseRow_sound (![1, 3, 5, 23] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_01_02_02_18) valid_01_02_02_18
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_02_18 Q := by
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
#print axioms Paper7MomentGapNumeric.row_01_02_02_18

theorem weighted_01_02_02_18 : b4RawGapContribution ![1, 2, 2, 18] = 24 := by
  calc
    b4RawGapContribution ![1, 2, 2, 18] = b4GapPatternWeight 2 2 18 * 1 :=
      b4GapContribution_from_row 1 2 2 18 1 row_01_02_02_18
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_18

theorem row_01_02_02_19 : b4RowContribution (![1, 3, 5, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 24] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 24 = 33
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 611 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 24^2 = 611
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_19

theorem weighted_01_02_02_19 : b4RawGapContribution ![1, 2, 2, 19] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 19] = b4GapPatternWeight 2 2 19 * 0 :=
      b4GapContribution_from_row 1 2 2 19 0 row_01_02_02_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_19

theorem row_01_02_02_20 : b4RowContribution (![1, 3, 5, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 25] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 25 = 34
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 660 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 25^2 = 660
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_20

theorem weighted_01_02_02_20 : b4RawGapContribution ![1, 2, 2, 20] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 20] = b4GapPatternWeight 2 2 20 * 0 :=
      b4GapContribution_from_row 1 2 2 20 0 row_01_02_02_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_20

theorem row_01_02_02_21 : b4RowContribution (![1, 3, 5, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 26] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 26 = 35
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 711 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 26^2 = 711
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_21

theorem weighted_01_02_02_21 : b4RawGapContribution ![1, 2, 2, 21] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 21] = b4GapPatternWeight 2 2 21 * 0 :=
      b4GapContribution_from_row 1 2 2 21 0 row_01_02_02_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_21

theorem row_01_02_02_22 : b4RowContribution (![1, 3, 5, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 27] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 27 = 36
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 764 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 27^2 = 764
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_22

theorem weighted_01_02_02_22 : b4RawGapContribution ![1, 2, 2, 22] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 22] = b4GapPatternWeight 2 2 22 * 0 :=
      b4GapContribution_from_row 1 2 2 22 0 row_01_02_02_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_22

theorem row_01_02_02_23 : b4RowContribution (![1, 3, 5, 28] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 5, 28] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 5 + 28 = 37
    decide
  have hzsq : (∑ i, (((![1, 3, 5, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 819 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 5^2 + 28^2 = 819
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_02_23

theorem weighted_01_02_02_23 : b4RawGapContribution ![1, 2, 2, 23] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 2, 23] = b4GapPatternWeight 2 2 23 * 0 :=
      b4GapContribution_from_row 1 2 2 23 0 row_01_02_02_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_02_23

def dvalues_01_02_02 : Fin 24 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2112, 0, 1152, 0, 0, 0, 0, 0, 24, 24, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_02_02

theorem dblock_01_02_02 : b4GapPatternDBlock 1 2 2 = 3312 := by
  calc
    b4GapPatternDBlock 1 2 2 = ∑ d : Fin 24, dvalues_01_02_02 d := by
      apply b4GapDBlock_of_rows 1 2 2 dvalues_01_02_02
      intro d
      fin_cases d
      · exact weighted_01_02_02_00
      · exact weighted_01_02_02_01
      · exact weighted_01_02_02_02
      · exact weighted_01_02_02_03
      · exact weighted_01_02_02_04
      · exact weighted_01_02_02_05
      · exact weighted_01_02_02_06
      · exact weighted_01_02_02_07
      · exact weighted_01_02_02_08
      · exact weighted_01_02_02_09
      · exact weighted_01_02_02_10
      · exact weighted_01_02_02_11
      · exact weighted_01_02_02_12
      · exact weighted_01_02_02_13
      · exact weighted_01_02_02_14
      · exact weighted_01_02_02_15
      · exact weighted_01_02_02_16
      · exact weighted_01_02_02_17
      · exact weighted_01_02_02_18
      · exact weighted_01_02_02_19
      · exact weighted_01_02_02_20
      · exact weighted_01_02_02_21
      · exact weighted_01_02_02_22
      · exact weighted_01_02_02_23
    _ = 3312 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_02_02

end Paper7MomentGapNumeric
