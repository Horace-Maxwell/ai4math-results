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

theorem row_04_00_00_00 : b4RowContribution (![4, 4, 4, 4] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 4] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 4 = 16
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 64 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 4^2 = 64
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_00

theorem weighted_04_00_00_00 : b4RawGapContribution ![4, 0, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 0] = b4GapPatternWeight 0 0 0 * 0 :=
      b4GapContribution_from_row 4 0 0 0 0 row_04_00_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_00

theorem row_04_00_00_01 : b4RowContribution (![4, 4, 4, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 5] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 5 = 17
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 73 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 5^2 = 73
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_01

theorem weighted_04_00_00_01 : b4RawGapContribution ![4, 0, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 1] = b4GapPatternWeight 0 0 1 * 0 :=
      b4GapContribution_from_row 4 0 0 1 0 row_04_00_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_01

theorem row_04_00_00_02 : b4RowContribution (![4, 4, 4, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 6] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 6 = 18
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 84 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 6^2 = 84
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_02

theorem weighted_04_00_00_02 : b4RawGapContribution ![4, 0, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 2] = b4GapPatternWeight 0 0 2 * 0 :=
      b4GapContribution_from_row 4 0 0 2 0 row_04_00_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_02

theorem row_04_00_00_03 : b4RowContribution (![4, 4, 4, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 7] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 7 = 19
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 97 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 7^2 = 97
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_03

theorem weighted_04_00_00_03 : b4RawGapContribution ![4, 0, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 3] = b4GapPatternWeight 0 0 3 * 0 :=
      b4GapContribution_from_row 4 0 0 3 0 row_04_00_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_03

theorem row_04_00_00_04 : b4RowContribution (![4, 4, 4, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 8] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 8 = 20
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 112 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 8^2 = 112
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_04

theorem weighted_04_00_00_04 : b4RawGapContribution ![4, 0, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 4] = b4GapPatternWeight 0 0 4 * 0 :=
      b4GapContribution_from_row 4 0 0 4 0 row_04_00_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_04

theorem row_04_00_00_05 : b4RowContribution (![4, 4, 4, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 9] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 9 = 21
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 129 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 9^2 = 129
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_05

theorem weighted_04_00_00_05 : b4RawGapContribution ![4, 0, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 5] = b4GapPatternWeight 0 0 5 * 0 :=
      b4GapContribution_from_row 4 0 0 5 0 row_04_00_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_05

theorem row_04_00_00_06 : b4RowContribution (![4, 4, 4, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 10] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 10 = 22
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 148 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 10^2 = 148
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_06

theorem weighted_04_00_00_06 : b4RawGapContribution ![4, 0, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 6] = b4GapPatternWeight 0 0 6 * 0 :=
      b4GapContribution_from_row 4 0 0 6 0 row_04_00_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_06

theorem row_04_00_00_07 : b4RowContribution (![4, 4, 4, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 11] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 11 = 23
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 169 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 11^2 = 169
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_07

theorem weighted_04_00_00_07 : b4RawGapContribution ![4, 0, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 7] = b4GapPatternWeight 0 0 7 * 0 :=
      b4GapContribution_from_row 4 0 0 7 0 row_04_00_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_07

theorem row_04_00_00_08 : b4RowContribution (![4, 4, 4, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 12] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 12 = 24
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 192 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 12^2 = 192
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_08

theorem weighted_04_00_00_08 : b4RawGapContribution ![4, 0, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 8] = b4GapPatternWeight 0 0 8 * 0 :=
      b4GapContribution_from_row 4 0 0 8 0 row_04_00_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_08

def layers_04_00_00_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 18, 19, 18, 15, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 35, 53, 72, 90, 105, 115, 121, 124, 125, 125, 124, 121, 115, 105, 90]]
#print axioms Paper7MomentGapNumeric.layers_04_00_00_09

theorem cells_04_00_00_09 : QTableValid (![4, 4, 4, 13] : Fin 4 → ℕ) layers_04_00_00_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_00_00_09

theorem valid_04_00_00_09 :
    SparseRowValid (![4, 4, 4, 13] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_04_00_00_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 4, 4, 13] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 4 + 4 + 4 + 13 = 25
      decide
    have hzsq : (∑ i, (((![4, 4, 4, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 217 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 4^2 + 4^2 + 13^2 = 217
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_00_00_09
#print axioms Paper7MomentGapNumeric.valid_04_00_00_09

def qvalues_04_00_00_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 121, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_00_00_09

theorem row_04_00_00_09 : b4RowContribution (![4, 4, 4, 13] : Fin 4 → ℕ) = 121 := by
  calc
    b4RowContribution (![4, 4, 4, 13] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_04_00_00_09) :=
      sparseRow_sound (![4, 4, 4, 13] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_04_00_00_09) valid_04_00_00_09
    _ = 121 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_00_00_09 Q := by
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
        _ = 121 := by decide
#print axioms Paper7MomentGapNumeric.row_04_00_00_09

theorem weighted_04_00_00_09 : b4RawGapContribution ![4, 0, 0, 9] = 484 := by
  calc
    b4RawGapContribution ![4, 0, 0, 9] = b4GapPatternWeight 0 0 9 * 121 :=
      b4GapContribution_from_row 4 0 0 9 121 row_04_00_00_09
    _ = 484 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_09

theorem row_04_00_00_10 : b4RowContribution (![4, 4, 4, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 14] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 14 = 26
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 244 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 14^2 = 244
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_10

theorem weighted_04_00_00_10 : b4RawGapContribution ![4, 0, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 10] = b4GapPatternWeight 0 0 10 * 0 :=
      b4GapContribution_from_row 4 0 0 10 0 row_04_00_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_10

def layers_04_00_00_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 18, 19, 18, 15, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 35, 53, 72, 90, 105, 115, 121, 124, 125, 125, 125, 125, 124, 121, 115]]
#print axioms Paper7MomentGapNumeric.layers_04_00_00_11

theorem cells_04_00_00_11 : QTableValid (![4, 4, 4, 15] : Fin 4 → ℕ) layers_04_00_00_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_00_00_11

theorem valid_04_00_00_11 :
    SparseRowValid (![4, 4, 4, 15] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_04_00_00_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 4, 4, 15] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 4 + 4 + 4 + 15 = 27
      decide
    have hzsq : (∑ i, (((![4, 4, 4, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 273 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 4^2 + 4^2 + 15^2 = 273
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_00_00_11
#print axioms Paper7MomentGapNumeric.valid_04_00_00_11

def qvalues_04_00_00_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 115, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_00_00_11

theorem row_04_00_00_11 : b4RowContribution (![4, 4, 4, 15] : Fin 4 → ℕ) = 115 := by
  calc
    b4RowContribution (![4, 4, 4, 15] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_04_00_00_11) :=
      sparseRow_sound (![4, 4, 4, 15] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_04_00_00_11) valid_04_00_00_11
    _ = 115 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_00_00_11 Q := by
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
        _ = 115 := by decide
#print axioms Paper7MomentGapNumeric.row_04_00_00_11

theorem weighted_04_00_00_11 : b4RawGapContribution ![4, 0, 0, 11] = 460 := by
  calc
    b4RawGapContribution ![4, 0, 0, 11] = b4GapPatternWeight 0 0 11 * 115 :=
      b4GapContribution_from_row 4 0 0 11 115 row_04_00_00_11
    _ = 460 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_11

theorem row_04_00_00_12 : b4RowContribution (![4, 4, 4, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 16] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 16 = 28
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 304 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 16^2 = 304
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_12

theorem weighted_04_00_00_12 : b4RawGapContribution ![4, 0, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 12] = b4GapPatternWeight 0 0 12 * 0 :=
      b4GapContribution_from_row 4 0 0 12 0 row_04_00_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_12

theorem row_04_00_00_13 : b4RowContribution (![4, 4, 4, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 17] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 17 = 29
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 337 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 17^2 = 337
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_13

theorem weighted_04_00_00_13 : b4RawGapContribution ![4, 0, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 13] = b4GapPatternWeight 0 0 13 * 0 :=
      b4GapContribution_from_row 4 0 0 13 0 row_04_00_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_13

theorem row_04_00_00_14 : b4RowContribution (![4, 4, 4, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 18] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 18 = 30
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 372 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 18^2 = 372
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_14

theorem weighted_04_00_00_14 : b4RawGapContribution ![4, 0, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 14] = b4GapPatternWeight 0 0 14 * 0 :=
      b4GapContribution_from_row 4 0 0 14 0 row_04_00_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_14

theorem row_04_00_00_15 : b4RowContribution (![4, 4, 4, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 19] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 19 = 31
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 409 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 19^2 = 409
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_15

theorem weighted_04_00_00_15 : b4RawGapContribution ![4, 0, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 15] = b4GapPatternWeight 0 0 15 * 0 :=
      b4GapContribution_from_row 4 0 0 15 0 row_04_00_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_15

theorem row_04_00_00_16 : b4RowContribution (![4, 4, 4, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 20] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 20 = 32
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 448 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 20^2 = 448
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_16

theorem weighted_04_00_00_16 : b4RawGapContribution ![4, 0, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 16] = b4GapPatternWeight 0 0 16 * 0 :=
      b4GapContribution_from_row 4 0 0 16 0 row_04_00_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_16

theorem row_04_00_00_17 : b4RowContribution (![4, 4, 4, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 21] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 21 = 33
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 489 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 21^2 = 489
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_17

theorem weighted_04_00_00_17 : b4RawGapContribution ![4, 0, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 17] = b4GapPatternWeight 0 0 17 * 0 :=
      b4GapContribution_from_row 4 0 0 17 0 row_04_00_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_17

theorem row_04_00_00_18 : b4RowContribution (![4, 4, 4, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 22] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 22 = 34
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 532 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 22^2 = 532
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_18

theorem weighted_04_00_00_18 : b4RawGapContribution ![4, 0, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 18] = b4GapPatternWeight 0 0 18 * 0 :=
      b4GapContribution_from_row 4 0 0 18 0 row_04_00_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_18

theorem row_04_00_00_19 : b4RowContribution (![4, 4, 4, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 23] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 23 = 35
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 577 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 23^2 = 577
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_19

theorem weighted_04_00_00_19 : b4RawGapContribution ![4, 0, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 19] = b4GapPatternWeight 0 0 19 * 0 :=
      b4GapContribution_from_row 4 0 0 19 0 row_04_00_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_19

theorem row_04_00_00_20 : b4RowContribution (![4, 4, 4, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 24] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 24 = 36
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 624 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 24^2 = 624
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_20

theorem weighted_04_00_00_20 : b4RawGapContribution ![4, 0, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 20] = b4GapPatternWeight 0 0 20 * 0 :=
      b4GapContribution_from_row 4 0 0 20 0 row_04_00_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_20

theorem row_04_00_00_21 : b4RowContribution (![4, 4, 4, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 4, 25] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 4 + 25 = 37
    decide
  have hzsq : (∑ i, (((![4, 4, 4, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 673 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 4^2 + 25^2 = 673
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_00_21

theorem weighted_04_00_00_21 : b4RawGapContribution ![4, 0, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 0, 21] = b4GapPatternWeight 0 0 21 * 0 :=
      b4GapContribution_from_row 4 0 0 21 0 row_04_00_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_00_21

def dvalues_04_00_00 : Fin 22 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 484, 0, 460, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_00_00

theorem dblock_04_00_00 : b4GapPatternDBlock 4 0 0 = 944 := by
  calc
    b4GapPatternDBlock 4 0 0 = ∑ d : Fin 22, dvalues_04_00_00 d := by
      apply b4GapDBlock_of_rows 4 0 0 dvalues_04_00_00
      intro d
      fin_cases d
      · exact weighted_04_00_00_00
      · exact weighted_04_00_00_01
      · exact weighted_04_00_00_02
      · exact weighted_04_00_00_03
      · exact weighted_04_00_00_04
      · exact weighted_04_00_00_05
      · exact weighted_04_00_00_06
      · exact weighted_04_00_00_07
      · exact weighted_04_00_00_08
      · exact weighted_04_00_00_09
      · exact weighted_04_00_00_10
      · exact weighted_04_00_00_11
      · exact weighted_04_00_00_12
      · exact weighted_04_00_00_13
      · exact weighted_04_00_00_14
      · exact weighted_04_00_00_15
      · exact weighted_04_00_00_16
      · exact weighted_04_00_00_17
      · exact weighted_04_00_00_18
      · exact weighted_04_00_00_19
      · exact weighted_04_00_00_20
      · exact weighted_04_00_00_21
    _ = 944 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_00_00

end Paper7MomentGapNumeric
