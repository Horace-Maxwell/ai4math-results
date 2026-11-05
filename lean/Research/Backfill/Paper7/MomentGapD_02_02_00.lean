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

theorem row_02_02_00_00 : b4RowContribution (![2, 4, 4, 4] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 4] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 4 = 14
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 52 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 4^2 = 52
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_00

theorem weighted_02_02_00_00 : b4RawGapContribution ![2, 2, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 0] = b4GapPatternWeight 2 0 0 * 0 :=
      b4GapContribution_from_row 2 2 0 0 0 row_02_02_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_00

theorem row_02_02_00_01 : b4RowContribution (![2, 4, 4, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 5] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 5 = 15
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 61 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 5^2 = 61
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_01

theorem weighted_02_02_00_01 : b4RawGapContribution ![2, 2, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 1] = b4GapPatternWeight 2 0 1 * 0 :=
      b4GapContribution_from_row 2 2 0 1 0 row_02_02_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_01

theorem row_02_02_00_02 : b4RowContribution (![2, 4, 4, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 6] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 6 = 16
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 72 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 6^2 = 72
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_02

theorem weighted_02_02_00_02 : b4RawGapContribution ![2, 2, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 2] = b4GapPatternWeight 2 0 2 * 0 :=
      b4GapContribution_from_row 2 2 0 2 0 row_02_02_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_02

theorem row_02_02_00_03 : b4RowContribution (![2, 4, 4, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 7] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 7 = 17
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 85 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 7^2 = 85
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_03

theorem weighted_02_02_00_03 : b4RawGapContribution ![2, 2, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 3] = b4GapPatternWeight 2 0 3 * 0 :=
      b4GapContribution_from_row 2 2 0 3 0 row_02_02_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_03

theorem row_02_02_00_04 : b4RowContribution (![2, 4, 4, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 8] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 8 = 18
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 100 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 8^2 = 100
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_04

theorem weighted_02_02_00_04 : b4RawGapContribution ![2, 2, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 4] = b4GapPatternWeight 2 0 4 * 0 :=
      b4GapContribution_from_row 2 2 0 4 0 row_02_02_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_04

theorem row_02_02_00_05 : b4RowContribution (![2, 4, 4, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 9] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 9 = 19
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 117 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 9^2 = 117
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_05

theorem weighted_02_02_00_05 : b4RawGapContribution ![2, 2, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 5] = b4GapPatternWeight 2 0 5 * 0 :=
      b4GapContribution_from_row 2 2 0 5 0 row_02_02_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_05

theorem row_02_02_00_06 : b4RowContribution (![2, 4, 4, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 10] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 10 = 20
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 136 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 10^2 = 136
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_06

theorem weighted_02_02_00_06 : b4RawGapContribution ![2, 2, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 6] = b4GapPatternWeight 2 0 6 * 0 :=
      b4GapContribution_from_row 2 2 0 6 0 row_02_02_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_06

theorem row_02_02_00_07 : b4RowContribution (![2, 4, 4, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 11] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 11 = 21
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 157 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 11^2 = 157
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_07

theorem weighted_02_02_00_07 : b4RawGapContribution ![2, 2, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 7] = b4GapPatternWeight 2 0 7 * 0 :=
      b4GapContribution_from_row 2 2 0 7 0 row_02_02_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_07

theorem row_02_02_00_08 : b4RowContribution (![2, 4, 4, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 12] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 12 = 22
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 180 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 12^2 = 180
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_08

theorem weighted_02_02_00_08 : b4RawGapContribution ![2, 2, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 8] = b4GapPatternWeight 2 0 8 * 0 :=
      b4GapContribution_from_row 2 2 0 8 0 row_02_02_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_08

theorem row_02_02_00_09 : b4RowContribution (![2, 4, 4, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 13] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 13 = 23
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 205 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 13^2 = 205
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_09

theorem weighted_02_02_00_09 : b4RawGapContribution ![2, 2, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 9] = b4GapPatternWeight 2 0 9 * 0 :=
      b4GapContribution_from_row 2 2 0 9 0 row_02_02_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_09

def layers_02_02_00_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 13, 12, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 31, 44, 56, 65, 71, 74, 75, 75, 75, 75, 75, 74, 71, 65, 56]]
#print axioms Paper7MomentGapNumeric.layers_02_02_00_10

theorem cells_02_02_00_10 : QTableValid (![2, 4, 4, 14] : Fin 4 → ℕ) layers_02_02_00_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_02_00_10

theorem valid_02_02_00_10 :
    SparseRowValid (![2, 4, 4, 14] : Fin 4 → ℕ) ({4, 10} : Finset (Fin 19)) (fun _ => layers_02_02_00_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 4, 4, 14] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 2 + 4 + 4 + 14 = 24
      decide
    have hzsq : (∑ i, (((![2, 4, 4, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 232 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 4^2 + 4^2 + 14^2 = 232
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_02_00_10
#print axioms Paper7MomentGapNumeric.valid_02_02_00_10

def qvalues_02_02_00_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 75, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_02_00_10

theorem row_02_02_00_10 : b4RowContribution (![2, 4, 4, 14] : Fin 4 → ℕ) = 106 := by
  calc
    b4RowContribution (![2, 4, 4, 14] : Fin 4 → ℕ) =
        sparseRowValue ({4, 10} : Finset (Fin 19)) (fun _ => layers_02_02_00_10) :=
      sparseRow_sound (![2, 4, 4, 14] : Fin 4 → ℕ) ({4, 10} : Finset (Fin 19)) (fun _ => layers_02_02_00_10) valid_02_02_00_10
    _ = 106 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_02_00_10 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 106 := by decide
#print axioms Paper7MomentGapNumeric.row_02_02_00_10

theorem weighted_02_02_00_10 : b4RawGapContribution ![2, 2, 0, 10] = 1272 := by
  calc
    b4RawGapContribution ![2, 2, 0, 10] = b4GapPatternWeight 2 0 10 * 106 :=
      b4GapContribution_from_row 2 2 0 10 106 row_02_02_00_10
    _ = 1272 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_10

theorem row_02_02_00_11 : b4RowContribution (![2, 4, 4, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 15] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 15 = 25
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 261 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 15^2 = 261
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_11

theorem weighted_02_02_00_11 : b4RawGapContribution ![2, 2, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 11] = b4GapPatternWeight 2 0 11 * 0 :=
      b4GapContribution_from_row 2 2 0 11 0 row_02_02_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_11

theorem row_02_02_00_12 : b4RowContribution (![2, 4, 4, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 16] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 16 = 26
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 292 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 16^2 = 292
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_12

theorem weighted_02_02_00_12 : b4RawGapContribution ![2, 2, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 12] = b4GapPatternWeight 2 0 12 * 0 :=
      b4GapContribution_from_row 2 2 0 12 0 row_02_02_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_12

theorem row_02_02_00_13 : b4RowContribution (![2, 4, 4, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 17] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 17 = 27
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 17^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_13

theorem weighted_02_02_00_13 : b4RawGapContribution ![2, 2, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 13] = b4GapPatternWeight 2 0 13 * 0 :=
      b4GapContribution_from_row 2 2 0 13 0 row_02_02_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_13

theorem row_02_02_00_14 : b4RowContribution (![2, 4, 4, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 18] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 18 = 28
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 360 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 18^2 = 360
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_14

theorem weighted_02_02_00_14 : b4RawGapContribution ![2, 2, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 14] = b4GapPatternWeight 2 0 14 * 0 :=
      b4GapContribution_from_row 2 2 0 14 0 row_02_02_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_14

theorem row_02_02_00_15 : b4RowContribution (![2, 4, 4, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 19] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 19 = 29
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 397 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 19^2 = 397
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_15

theorem weighted_02_02_00_15 : b4RawGapContribution ![2, 2, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 15] = b4GapPatternWeight 2 0 15 * 0 :=
      b4GapContribution_from_row 2 2 0 15 0 row_02_02_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_15

theorem row_02_02_00_16 : b4RowContribution (![2, 4, 4, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 20] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 20 = 30
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 436 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 20^2 = 436
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_16

theorem weighted_02_02_00_16 : b4RawGapContribution ![2, 2, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 16] = b4GapPatternWeight 2 0 16 * 0 :=
      b4GapContribution_from_row 2 2 0 16 0 row_02_02_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_16

theorem row_02_02_00_17 : b4RowContribution (![2, 4, 4, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 21] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 21 = 31
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 477 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 21^2 = 477
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_17

theorem weighted_02_02_00_17 : b4RawGapContribution ![2, 2, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 17] = b4GapPatternWeight 2 0 17 * 0 :=
      b4GapContribution_from_row 2 2 0 17 0 row_02_02_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_17

theorem row_02_02_00_18 : b4RowContribution (![2, 4, 4, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 22] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 22 = 32
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 520 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 22^2 = 520
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_18

theorem weighted_02_02_00_18 : b4RawGapContribution ![2, 2, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 18] = b4GapPatternWeight 2 0 18 * 0 :=
      b4GapContribution_from_row 2 2 0 18 0 row_02_02_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_18

def layers_02_02_00_19 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 13, 12, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 19, 31, 44, 56, 65, 71, 74, 75, 75, 75, 75, 75, 75, 75, 75, 75]]
#print axioms Paper7MomentGapNumeric.layers_02_02_00_19

theorem cells_02_02_00_19 : QTableValid (![2, 4, 4, 23] : Fin 4 → ℕ) layers_02_02_00_19 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_02_00_19

theorem valid_02_02_00_19 :
    SparseRowValid (![2, 4, 4, 23] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_02_00_19) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 4, 4, 23] : Fin 4 → ℕ) i) = 33 := by
      rw [Fin.sum_univ_four]
      change 2 + 4 + 4 + 23 = 33
      decide
    have hzsq : (∑ i, (((![2, 4, 4, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 565 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 4^2 + 4^2 + 23^2 = 565
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_02_00_19
#print axioms Paper7MomentGapNumeric.valid_02_02_00_19

def qvalues_02_02_00_19 : Fin 19 → ℕ := ![0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_02_00_19

theorem row_02_02_00_19 : b4RowContribution (![2, 4, 4, 23] : Fin 4 → ℕ) = 31 := by
  calc
    b4RowContribution (![2, 4, 4, 23] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_02_02_00_19) :=
      sparseRow_sound (![2, 4, 4, 23] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_02_00_19) valid_02_02_00_19
    _ = 31 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_02_00_19 Q := by
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
#print axioms Paper7MomentGapNumeric.row_02_02_00_19

theorem weighted_02_02_00_19 : b4RawGapContribution ![2, 2, 0, 19] = 372 := by
  calc
    b4RawGapContribution ![2, 2, 0, 19] = b4GapPatternWeight 2 0 19 * 31 :=
      b4GapContribution_from_row 2 2 0 19 31 row_02_02_00_19
    _ = 372 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_19

theorem row_02_02_00_20 : b4RowContribution (![2, 4, 4, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 24] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 24 = 34
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 612 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 24^2 = 612
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_20

theorem weighted_02_02_00_20 : b4RawGapContribution ![2, 2, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 20] = b4GapPatternWeight 2 0 20 * 0 :=
      b4GapContribution_from_row 2 2 0 20 0 row_02_02_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_20

theorem row_02_02_00_21 : b4RowContribution (![2, 4, 4, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 25] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 25 = 35
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 661 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 25^2 = 661
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_21

theorem weighted_02_02_00_21 : b4RawGapContribution ![2, 2, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 21] = b4GapPatternWeight 2 0 21 * 0 :=
      b4GapContribution_from_row 2 2 0 21 0 row_02_02_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_21

theorem row_02_02_00_22 : b4RowContribution (![2, 4, 4, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 26] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 26 = 36
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 712 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 26^2 = 712
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_22

theorem weighted_02_02_00_22 : b4RawGapContribution ![2, 2, 0, 22] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 22] = b4GapPatternWeight 2 0 22 * 0 :=
      b4GapContribution_from_row 2 2 0 22 0 row_02_02_00_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_22

theorem row_02_02_00_23 : b4RowContribution (![2, 4, 4, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 4, 27] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 4 + 27 = 37
    decide
  have hzsq : (∑ i, (((![2, 4, 4, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 765 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 4^2 + 27^2 = 765
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_00_23

theorem weighted_02_02_00_23 : b4RawGapContribution ![2, 2, 0, 23] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 0, 23] = b4GapPatternWeight 2 0 23 * 0 :=
      b4GapContribution_from_row 2 2 0 23 0 row_02_02_00_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_00_23

def dvalues_02_02_00 : Fin 24 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1272, 0, 0, 0, 0, 0, 0, 0, 0, 372, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_02_00

theorem dblock_02_02_00 : b4GapPatternDBlock 2 2 0 = 1644 := by
  calc
    b4GapPatternDBlock 2 2 0 = ∑ d : Fin 24, dvalues_02_02_00 d := by
      apply b4GapDBlock_of_rows 2 2 0 dvalues_02_02_00
      intro d
      fin_cases d
      · exact weighted_02_02_00_00
      · exact weighted_02_02_00_01
      · exact weighted_02_02_00_02
      · exact weighted_02_02_00_03
      · exact weighted_02_02_00_04
      · exact weighted_02_02_00_05
      · exact weighted_02_02_00_06
      · exact weighted_02_02_00_07
      · exact weighted_02_02_00_08
      · exact weighted_02_02_00_09
      · exact weighted_02_02_00_10
      · exact weighted_02_02_00_11
      · exact weighted_02_02_00_12
      · exact weighted_02_02_00_13
      · exact weighted_02_02_00_14
      · exact weighted_02_02_00_15
      · exact weighted_02_02_00_16
      · exact weighted_02_02_00_17
      · exact weighted_02_02_00_18
      · exact weighted_02_02_00_19
      · exact weighted_02_02_00_20
      · exact weighted_02_02_00_21
      · exact weighted_02_02_00_22
      · exact weighted_02_02_00_23
    _ = 1644 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_02_00

end Paper7MomentGapNumeric
