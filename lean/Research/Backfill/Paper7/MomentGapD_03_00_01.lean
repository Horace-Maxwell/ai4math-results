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

theorem row_03_00_01_00 : b4RowContribution (![3, 3, 4, 4] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 4] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 4 = 14
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 50 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 4^2 = 50
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_00

theorem weighted_03_00_01_00 : b4RawGapContribution ![3, 0, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 0] = b4GapPatternWeight 0 1 0 * 0 :=
      b4GapContribution_from_row 3 0 1 0 0 row_03_00_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_00

theorem row_03_00_01_01 : b4RowContribution (![3, 3, 4, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 5] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 5 = 15
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 59 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 5^2 = 59
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_01

theorem weighted_03_00_01_01 : b4RawGapContribution ![3, 0, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 1] = b4GapPatternWeight 0 1 1 * 0 :=
      b4GapContribution_from_row 3 0 1 1 0 row_03_00_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_01

theorem row_03_00_01_02 : b4RowContribution (![3, 3, 4, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 6] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 6 = 16
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 70 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 6^2 = 70
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_02

theorem weighted_03_00_01_02 : b4RawGapContribution ![3, 0, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 2] = b4GapPatternWeight 0 1 2 * 0 :=
      b4GapContribution_from_row 3 0 1 2 0 row_03_00_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_02

theorem row_03_00_01_03 : b4RowContribution (![3, 3, 4, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 7] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 7 = 17
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 83 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 7^2 = 83
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_03

theorem weighted_03_00_01_03 : b4RawGapContribution ![3, 0, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 3] = b4GapPatternWeight 0 1 3 * 0 :=
      b4GapContribution_from_row 3 0 1 3 0 row_03_00_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_03

theorem row_03_00_01_04 : b4RowContribution (![3, 3, 4, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 8] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 8 = 18
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 98 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 8^2 = 98
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_04

theorem weighted_03_00_01_04 : b4RawGapContribution ![3, 0, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 4] = b4GapPatternWeight 0 1 4 * 0 :=
      b4GapContribution_from_row 3 0 1 4 0 row_03_00_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_04

theorem row_03_00_01_05 : b4RowContribution (![3, 3, 4, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 9] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 9 = 19
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 115 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 9^2 = 115
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_05

theorem weighted_03_00_01_05 : b4RawGapContribution ![3, 0, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 5] = b4GapPatternWeight 0 1 5 * 0 :=
      b4GapContribution_from_row 3 0 1 5 0 row_03_00_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_05

theorem row_03_00_01_06 : b4RowContribution (![3, 3, 4, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 10] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 10 = 20
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 134 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 10^2 = 134
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_06

theorem weighted_03_00_01_06 : b4RawGapContribution ![3, 0, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 6] = b4GapPatternWeight 0 1 6 * 0 :=
      b4GapContribution_from_row 3 0 1 6 0 row_03_00_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_06

theorem row_03_00_01_07 : b4RowContribution (![3, 3, 4, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 11] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 11 = 21
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 155 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 11^2 = 155
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_07

theorem weighted_03_00_01_07 : b4RawGapContribution ![3, 0, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 7] = b4GapPatternWeight 0 1 7 * 0 :=
      b4GapContribution_from_row 3 0 1 7 0 row_03_00_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_07

theorem row_03_00_01_08 : b4RowContribution (![3, 3, 4, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 12] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 12 = 22
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 178 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 12^2 = 178
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_08

theorem weighted_03_00_01_08 : b4RawGapContribution ![3, 0, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 8] = b4GapPatternWeight 0 1 8 * 0 :=
      b4GapContribution_from_row 3 0 1 8 0 row_03_00_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_08

theorem row_03_00_01_09 : b4RowContribution (![3, 3, 4, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 13] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 13 = 23
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 203 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 13^2 = 203
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_09

theorem weighted_03_00_01_09 : b4RawGapContribution ![3, 0, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 9] = b4GapPatternWeight 0 1 9 * 0 :=
      b4GapContribution_from_row 3 0 1 9 0 row_03_00_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_09

def layers_03_00_01_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 14, 13, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 33, 47, 60, 70, 76, 79, 80, 80, 80, 80, 80, 79, 76, 70, 60]]
#print axioms Paper7MomentGapNumeric.layers_03_00_01_10

theorem cells_03_00_01_10 : QTableValid (![3, 3, 4, 14] : Fin 4 → ℕ) layers_03_00_01_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_00_01_10

theorem valid_03_00_01_10 :
    SparseRowValid (![3, 3, 4, 14] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_03_00_01_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 3, 4, 14] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 3 + 3 + 4 + 14 = 24
      decide
    have hzsq : (∑ i, (((![3, 3, 4, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 230 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 3^2 + 4^2 + 14^2 = 230
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_00_01_10
#print axioms Paper7MomentGapNumeric.valid_03_00_01_10

def qvalues_03_00_01_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_00_01_10

theorem row_03_00_01_10 : b4RowContribution (![3, 3, 4, 14] : Fin 4 → ℕ) = 127 := by
  calc
    b4RowContribution (![3, 3, 4, 14] : Fin 4 → ℕ) =
        sparseRowValue ({5, 11} : Finset (Fin 19)) (fun _ => layers_03_00_01_10) :=
      sparseRow_sound (![3, 3, 4, 14] : Fin 4 → ℕ) ({5, 11} : Finset (Fin 19)) (fun _ => layers_03_00_01_10) valid_03_00_01_10
    _ = 127 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_00_01_10 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 127 := by decide
#print axioms Paper7MomentGapNumeric.row_03_00_01_10

theorem weighted_03_00_01_10 : b4RawGapContribution ![3, 0, 1, 10] = 1524 := by
  calc
    b4RawGapContribution ![3, 0, 1, 10] = b4GapPatternWeight 0 1 10 * 127 :=
      b4GapContribution_from_row 3 0 1 10 127 row_03_00_01_10
    _ = 1524 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_10

theorem row_03_00_01_11 : b4RowContribution (![3, 3, 4, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 15] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 15 = 25
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 259 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 15^2 = 259
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_11

theorem weighted_03_00_01_11 : b4RawGapContribution ![3, 0, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 11] = b4GapPatternWeight 0 1 11 * 0 :=
      b4GapContribution_from_row 3 0 1 11 0 row_03_00_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_11

def layers_03_00_01_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 14, 13, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 33, 47, 60, 70, 76, 79, 80, 80, 80, 80, 80, 80, 80, 79, 76]]
#print axioms Paper7MomentGapNumeric.layers_03_00_01_12

theorem cells_03_00_01_12 : QTableValid (![3, 3, 4, 16] : Fin 4 → ℕ) layers_03_00_01_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_00_01_12

theorem valid_03_00_01_12 :
    SparseRowValid (![3, 3, 4, 16] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_03_00_01_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 3, 4, 16] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 3 + 3 + 4 + 16 = 26
      decide
    have hzsq : (∑ i, (((![3, 3, 4, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 290 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 3^2 + 4^2 + 16^2 = 290
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_00_01_12
#print axioms Paper7MomentGapNumeric.valid_03_00_01_12

def qvalues_03_00_01_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_00_01_12

theorem row_03_00_01_12 : b4RowContribution (![3, 3, 4, 16] : Fin 4 → ℕ) = 76 := by
  calc
    b4RowContribution (![3, 3, 4, 16] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_03_00_01_12) :=
      sparseRow_sound (![3, 3, 4, 16] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_03_00_01_12) valid_03_00_01_12
    _ = 76 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_00_01_12 Q := by
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
        _ = 76 := by decide
#print axioms Paper7MomentGapNumeric.row_03_00_01_12

theorem weighted_03_00_01_12 : b4RawGapContribution ![3, 0, 1, 12] = 912 := by
  calc
    b4RawGapContribution ![3, 0, 1, 12] = b4GapPatternWeight 0 1 12 * 76 :=
      b4GapContribution_from_row 3 0 1 12 76 row_03_00_01_12
    _ = 912 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_12

theorem row_03_00_01_13 : b4RowContribution (![3, 3, 4, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 17] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 17 = 27
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 323 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 17^2 = 323
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_13

theorem weighted_03_00_01_13 : b4RawGapContribution ![3, 0, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 13] = b4GapPatternWeight 0 1 13 * 0 :=
      b4GapContribution_from_row 3 0 1 13 0 row_03_00_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_13

theorem row_03_00_01_14 : b4RowContribution (![3, 3, 4, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 18] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 18 = 28
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 358 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 18^2 = 358
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_14

theorem weighted_03_00_01_14 : b4RawGapContribution ![3, 0, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 14] = b4GapPatternWeight 0 1 14 * 0 :=
      b4GapContribution_from_row 3 0 1 14 0 row_03_00_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_14

theorem row_03_00_01_15 : b4RowContribution (![3, 3, 4, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 19] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 19 = 29
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 395 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 19^2 = 395
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_15

theorem weighted_03_00_01_15 : b4RawGapContribution ![3, 0, 1, 15] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 15] = b4GapPatternWeight 0 1 15 * 0 :=
      b4GapContribution_from_row 3 0 1 15 0 row_03_00_01_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_15

theorem row_03_00_01_16 : b4RowContribution (![3, 3, 4, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 20] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 20 = 30
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 434 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 20^2 = 434
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_16

theorem weighted_03_00_01_16 : b4RawGapContribution ![3, 0, 1, 16] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 16] = b4GapPatternWeight 0 1 16 * 0 :=
      b4GapContribution_from_row 3 0 1 16 0 row_03_00_01_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_16

theorem row_03_00_01_17 : b4RowContribution (![3, 3, 4, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 21] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 21 = 31
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 475 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 21^2 = 475
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_17

theorem weighted_03_00_01_17 : b4RawGapContribution ![3, 0, 1, 17] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 17] = b4GapPatternWeight 0 1 17 * 0 :=
      b4GapContribution_from_row 3 0 1 17 0 row_03_00_01_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_17

theorem row_03_00_01_18 : b4RowContribution (![3, 3, 4, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 22] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 22 = 32
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 518 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 22^2 = 518
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_18

theorem weighted_03_00_01_18 : b4RawGapContribution ![3, 0, 1, 18] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 18] = b4GapPatternWeight 0 1 18 * 0 :=
      b4GapContribution_from_row 3 0 1 18 0 row_03_00_01_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_18

theorem row_03_00_01_19 : b4RowContribution (![3, 3, 4, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 23] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 23 = 33
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 563 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 23^2 = 563
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_19

theorem weighted_03_00_01_19 : b4RawGapContribution ![3, 0, 1, 19] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 19] = b4GapPatternWeight 0 1 19 * 0 :=
      b4GapContribution_from_row 3 0 1 19 0 row_03_00_01_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_19

theorem row_03_00_01_20 : b4RowContribution (![3, 3, 4, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 24] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 24 = 34
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 610 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 24^2 = 610
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_20

theorem weighted_03_00_01_20 : b4RawGapContribution ![3, 0, 1, 20] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 20] = b4GapPatternWeight 0 1 20 * 0 :=
      b4GapContribution_from_row 3 0 1 20 0 row_03_00_01_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_20

theorem row_03_00_01_21 : b4RowContribution (![3, 3, 4, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 25] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 25 = 35
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 659 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 25^2 = 659
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_21

theorem weighted_03_00_01_21 : b4RawGapContribution ![3, 0, 1, 21] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 21] = b4GapPatternWeight 0 1 21 * 0 :=
      b4GapContribution_from_row 3 0 1 21 0 row_03_00_01_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_21

theorem row_03_00_01_22 : b4RowContribution (![3, 3, 4, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 26] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 26 = 36
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 710 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 26^2 = 710
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_22

theorem weighted_03_00_01_22 : b4RawGapContribution ![3, 0, 1, 22] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 22] = b4GapPatternWeight 0 1 22 * 0 :=
      b4GapContribution_from_row 3 0 1 22 0 row_03_00_01_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_22

theorem row_03_00_01_23 : b4RowContribution (![3, 3, 4, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 4, 27] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 4 + 27 = 37
    decide
  have hzsq : (∑ i, (((![3, 3, 4, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 763 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 4^2 + 27^2 = 763
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_01_23

theorem weighted_03_00_01_23 : b4RawGapContribution ![3, 0, 1, 23] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 1, 23] = b4GapPatternWeight 0 1 23 * 0 :=
      b4GapContribution_from_row 3 0 1 23 0 row_03_00_01_23
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_01_23

def dvalues_03_00_01 : Fin 24 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1524, 0, 912, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_00_01

theorem dblock_03_00_01 : b4GapPatternDBlock 3 0 1 = 2436 := by
  calc
    b4GapPatternDBlock 3 0 1 = ∑ d : Fin 24, dvalues_03_00_01 d := by
      apply b4GapDBlock_of_rows 3 0 1 dvalues_03_00_01
      intro d
      fin_cases d
      · exact weighted_03_00_01_00
      · exact weighted_03_00_01_01
      · exact weighted_03_00_01_02
      · exact weighted_03_00_01_03
      · exact weighted_03_00_01_04
      · exact weighted_03_00_01_05
      · exact weighted_03_00_01_06
      · exact weighted_03_00_01_07
      · exact weighted_03_00_01_08
      · exact weighted_03_00_01_09
      · exact weighted_03_00_01_10
      · exact weighted_03_00_01_11
      · exact weighted_03_00_01_12
      · exact weighted_03_00_01_13
      · exact weighted_03_00_01_14
      · exact weighted_03_00_01_15
      · exact weighted_03_00_01_16
      · exact weighted_03_00_01_17
      · exact weighted_03_00_01_18
      · exact weighted_03_00_01_19
      · exact weighted_03_00_01_20
      · exact weighted_03_00_01_21
      · exact weighted_03_00_01_22
      · exact weighted_03_00_01_23
    _ = 2436 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_00_01

end Paper7MomentGapNumeric
