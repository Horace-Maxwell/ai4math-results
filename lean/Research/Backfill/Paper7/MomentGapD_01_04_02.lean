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

theorem row_01_04_02_00 : b4RowContribution (![1, 5, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 7] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 7 = 20
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 124 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 7^2 = 124
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_00

theorem weighted_01_04_02_00 : b4RawGapContribution ![1, 4, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 0] = b4GapPatternWeight 4 2 0 * 0 :=
      b4GapContribution_from_row 1 4 2 0 0 row_01_04_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_00

theorem row_01_04_02_01 : b4RowContribution (![1, 5, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 8] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 8 = 21
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 139 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 8^2 = 139
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_01

theorem weighted_01_04_02_01 : b4RawGapContribution ![1, 4, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 1] = b4GapPatternWeight 4 2 1 * 0 :=
      b4GapContribution_from_row 1 4 2 1 0 row_01_04_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_01

theorem row_01_04_02_02 : b4RowContribution (![1, 5, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 9] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 9 = 22
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 156 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 9^2 = 156
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_02

theorem weighted_01_04_02_02 : b4RawGapContribution ![1, 4, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 2] = b4GapPatternWeight 4 2 2 * 0 :=
      b4GapContribution_from_row 1 4 2 2 0 row_01_04_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_02

theorem row_01_04_02_03 : b4RowContribution (![1, 5, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 10] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 10 = 23
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 175 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 10^2 = 175
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_03

theorem weighted_01_04_02_03 : b4RawGapContribution ![1, 4, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 3] = b4GapPatternWeight 4 2 3 * 0 :=
      b4GapContribution_from_row 1 4 2 3 0 row_01_04_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_03

theorem row_01_04_02_04 : b4RowContribution (![1, 5, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 11] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 11 = 24
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 196 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 11^2 = 196
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_04

theorem weighted_01_04_02_04 : b4RawGapContribution ![1, 4, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 4] = b4GapPatternWeight 4 2 4 * 0 :=
      b4GapContribution_from_row 1 4 2 4 0 row_01_04_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_04

def layers_01_04_02_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 12, 12, 11, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 36, 48, 60, 71, 80, 87, 92, 95, 95, 92, 87, 80, 71, 60]]
#print axioms Paper7MomentGapNumeric.layers_01_04_02_05

theorem cells_01_04_02_05 : QTableValid (![1, 5, 7, 12] : Fin 4 → ℕ) layers_01_04_02_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_04_02_05

theorem valid_01_04_02_05 :
    SparseRowValid (![1, 5, 7, 12] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_04_02_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 5, 7, 12] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 1 + 5 + 7 + 12 = 25
      decide
    have hzsq : (∑ i, (((![1, 5, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 219 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 5^2 + 7^2 + 12^2 = 219
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_04_02_05
#print axioms Paper7MomentGapNumeric.valid_01_04_02_05

def qvalues_01_04_02_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_04_02_05

theorem row_01_04_02_05 : b4RowContribution (![1, 5, 7, 12] : Fin 4 → ℕ) = 80 := by
  calc
    b4RowContribution (![1, 5, 7, 12] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_01_04_02_05) :=
      sparseRow_sound (![1, 5, 7, 12] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_01_04_02_05) valid_01_04_02_05
    _ = 80 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_04_02_05 Q := by
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
        _ = 80 := by decide
#print axioms Paper7MomentGapNumeric.row_01_04_02_05

theorem weighted_01_04_02_05 : b4RawGapContribution ![1, 4, 2, 5] = 1920 := by
  calc
    b4RawGapContribution ![1, 4, 2, 5] = b4GapPatternWeight 4 2 5 * 80 :=
      b4GapContribution_from_row 1 4 2 5 80 row_01_04_02_05
    _ = 1920 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_05

theorem row_01_04_02_06 : b4RowContribution (![1, 5, 7, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 13] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 13 = 26
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 244 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 13^2 = 244
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_06

theorem weighted_01_04_02_06 : b4RawGapContribution ![1, 4, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 6] = b4GapPatternWeight 4 2 6 * 0 :=
      b4GapContribution_from_row 1 4 2 6 0 row_01_04_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_06

def layers_01_04_02_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 12, 12, 11, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 36, 48, 60, 71, 80, 87, 92, 95, 96, 96, 95, 92, 87, 80]]
#print axioms Paper7MomentGapNumeric.layers_01_04_02_07

theorem cells_01_04_02_07 : QTableValid (![1, 5, 7, 14] : Fin 4 → ℕ) layers_01_04_02_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_04_02_07

theorem valid_01_04_02_07 :
    SparseRowValid (![1, 5, 7, 14] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_04_02_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 5, 7, 14] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 1 + 5 + 7 + 14 = 27
      decide
    have hzsq : (∑ i, (((![1, 5, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 271 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 5^2 + 7^2 + 14^2 = 271
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_04_02_07
#print axioms Paper7MomentGapNumeric.valid_01_04_02_07

def qvalues_01_04_02_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 87, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_04_02_07

theorem row_01_04_02_07 : b4RowContribution (![1, 5, 7, 14] : Fin 4 → ℕ) = 87 := by
  calc
    b4RowContribution (![1, 5, 7, 14] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_04_02_07) :=
      sparseRow_sound (![1, 5, 7, 14] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_04_02_07) valid_01_04_02_07
    _ = 87 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_04_02_07 Q := by
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
        _ = 87 := by decide
#print axioms Paper7MomentGapNumeric.row_01_04_02_07

theorem weighted_01_04_02_07 : b4RawGapContribution ![1, 4, 2, 7] = 2088 := by
  calc
    b4RawGapContribution ![1, 4, 2, 7] = b4GapPatternWeight 4 2 7 * 87 :=
      b4GapContribution_from_row 1 4 2 7 87 row_01_04_02_07
    _ = 2088 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_07

theorem row_01_04_02_08 : b4RowContribution (![1, 5, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 15] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 15 = 28
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 300 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 15^2 = 300
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_08

theorem weighted_01_04_02_08 : b4RawGapContribution ![1, 4, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 8] = b4GapPatternWeight 4 2 8 * 0 :=
      b4GapContribution_from_row 1 4 2 8 0 row_01_04_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_08

theorem row_01_04_02_09 : b4RowContribution (![1, 5, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 16 = 29
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 331 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 16^2 = 331
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_09

theorem weighted_01_04_02_09 : b4RawGapContribution ![1, 4, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 9] = b4GapPatternWeight 4 2 9 * 0 :=
      b4GapContribution_from_row 1 4 2 9 0 row_01_04_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_09

theorem row_01_04_02_10 : b4RowContribution (![1, 5, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 17 = 30
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 364 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 17^2 = 364
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_10

theorem weighted_01_04_02_10 : b4RawGapContribution ![1, 4, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 10] = b4GapPatternWeight 4 2 10 * 0 :=
      b4GapContribution_from_row 1 4 2 10 0 row_01_04_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_10

theorem row_01_04_02_11 : b4RowContribution (![1, 5, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 18 = 31
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 399 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 18^2 = 399
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_11

theorem weighted_01_04_02_11 : b4RawGapContribution ![1, 4, 2, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 11] = b4GapPatternWeight 4 2 11 * 0 :=
      b4GapContribution_from_row 1 4 2 11 0 row_01_04_02_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_11

theorem row_01_04_02_12 : b4RowContribution (![1, 5, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 19 = 32
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 436 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 19^2 = 436
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_12

theorem weighted_01_04_02_12 : b4RawGapContribution ![1, 4, 2, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 12] = b4GapPatternWeight 4 2 12 * 0 :=
      b4GapContribution_from_row 1 4 2 12 0 row_01_04_02_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_12

theorem row_01_04_02_13 : b4RowContribution (![1, 5, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 20 = 33
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 475 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 20^2 = 475
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_13

theorem weighted_01_04_02_13 : b4RawGapContribution ![1, 4, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 13] = b4GapPatternWeight 4 2 13 * 0 :=
      b4GapContribution_from_row 1 4 2 13 0 row_01_04_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_13

theorem row_01_04_02_14 : b4RowContribution (![1, 5, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 21] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 21 = 34
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 516 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 21^2 = 516
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_14

theorem weighted_01_04_02_14 : b4RawGapContribution ![1, 4, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 14] = b4GapPatternWeight 4 2 14 * 0 :=
      b4GapContribution_from_row 1 4 2 14 0 row_01_04_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_14

theorem row_01_04_02_15 : b4RowContribution (![1, 5, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 22 = 35
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 559 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 22^2 = 559
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_15

theorem weighted_01_04_02_15 : b4RawGapContribution ![1, 4, 2, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 15] = b4GapPatternWeight 4 2 15 * 0 :=
      b4GapContribution_from_row 1 4 2 15 0 row_01_04_02_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_15

theorem row_01_04_02_16 : b4RowContribution (![1, 5, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 23 = 36
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 604 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 23^2 = 604
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_16

theorem weighted_01_04_02_16 : b4RawGapContribution ![1, 4, 2, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 16] = b4GapPatternWeight 4 2 16 * 0 :=
      b4GapContribution_from_row 1 4 2 16 0 row_01_04_02_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_16

theorem row_01_04_02_17 : b4RowContribution (![1, 5, 7, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 5, 7, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 5 + 7 + 24 = 37
    decide
  have hzsq : (∑ i, (((![1, 5, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 651 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 5^2 + 7^2 + 24^2 = 651
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_04_02_17

theorem weighted_01_04_02_17 : b4RawGapContribution ![1, 4, 2, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 4, 2, 17] = b4GapPatternWeight 4 2 17 * 0 :=
      b4GapContribution_from_row 1 4 2 17 0 row_01_04_02_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_04_02_17

def dvalues_01_04_02 : Fin 18 → ℕ := ![0, 0, 0, 0, 0, 1920, 0, 2088, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_04_02

theorem dblock_01_04_02 : b4GapPatternDBlock 1 4 2 = 4008 := by
  calc
    b4GapPatternDBlock 1 4 2 = ∑ d : Fin 18, dvalues_01_04_02 d := by
      apply b4GapDBlock_of_rows 1 4 2 dvalues_01_04_02
      intro d
      fin_cases d
      · exact weighted_01_04_02_00
      · exact weighted_01_04_02_01
      · exact weighted_01_04_02_02
      · exact weighted_01_04_02_03
      · exact weighted_01_04_02_04
      · exact weighted_01_04_02_05
      · exact weighted_01_04_02_06
      · exact weighted_01_04_02_07
      · exact weighted_01_04_02_08
      · exact weighted_01_04_02_09
      · exact weighted_01_04_02_10
      · exact weighted_01_04_02_11
      · exact weighted_01_04_02_12
      · exact weighted_01_04_02_13
      · exact weighted_01_04_02_14
      · exact weighted_01_04_02_15
      · exact weighted_01_04_02_16
      · exact weighted_01_04_02_17
    _ = 4008 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_04_02

end Paper7MomentGapNumeric
