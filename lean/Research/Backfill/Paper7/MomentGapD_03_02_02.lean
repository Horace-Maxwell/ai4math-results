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

theorem row_03_02_02_00 : b4RowContribution (![3, 5, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 7, 7] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 7 + 7 = 22
    decide
  have hzsq : (∑ i, (((![3, 5, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 132 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 7^2 + 7^2 = 132
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_02_00

theorem weighted_03_02_02_00 : b4RawGapContribution ![3, 2, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 2, 0] = b4GapPatternWeight 2 2 0 * 0 :=
      b4GapContribution_from_row 3 2 2 0 0 row_03_02_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_00

theorem row_03_02_02_01 : b4RowContribution (![3, 5, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 7, 8] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 7 + 8 = 23
    decide
  have hzsq : (∑ i, (((![3, 5, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 147 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 7^2 + 8^2 = 147
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_02_01

theorem weighted_03_02_02_01 : b4RawGapContribution ![3, 2, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 2, 1] = b4GapPatternWeight 2 2 1 * 0 :=
      b4GapContribution_from_row 3 2 2 1 0 row_03_02_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_01

theorem row_03_02_02_02 : b4RowContribution (![3, 5, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 7, 9] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 7 + 9 = 24
    decide
  have hzsq : (∑ i, (((![3, 5, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 164 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 7^2 + 9^2 = 164
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_02_02

theorem weighted_03_02_02_02 : b4RawGapContribution ![3, 2, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 2, 2] = b4GapPatternWeight 2 2 2 * 0 :=
      b4GapContribution_from_row 3 2 2 2 0 row_03_02_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_02

theorem row_03_02_02_03 : b4RowContribution (![3, 5, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 7, 10] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 7 + 10 = 25
    decide
  have hzsq : (∑ i, (((![3, 5, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 183 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 7^2 + 10^2 = 183
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_02_03

theorem weighted_03_02_02_03 : b4RawGapContribution ![3, 2, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 2, 3] = b4GapPatternWeight 2 2 3 * 0 :=
      b4GapContribution_from_row 3 2 2 3 0 row_03_02_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_03

theorem row_03_02_02_04 : b4RowContribution (![3, 5, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 7, 11] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 7 + 11 = 26
    decide
  have hzsq : (∑ i, (((![3, 5, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 204 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 7^2 + 11^2 = 204
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_02_04

theorem weighted_03_02_02_04 : b4RawGapContribution ![3, 2, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 2, 4] = b4GapPatternWeight 2 2 4 * 0 :=
      b4GapContribution_from_row 3 2 2 4 0 row_03_02_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_04

def layers_03_02_02_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 21, 23, 23, 21, 18, 14, 10, 6, 3, 1, 0, 0, 0], ![1, 4, 10, 20, 34, 52, 73, 96, 119, 140, 158, 172, 182, 187, 187, 182, 172, 158, 140]]
#print axioms Paper7MomentGapNumeric.layers_03_02_02_05

theorem cells_03_02_02_05 : QTableValid (![3, 5, 7, 12] : Fin 4 → ℕ) layers_03_02_02_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_02_02_05

theorem valid_03_02_02_05 :
    SparseRowValid (![3, 5, 7, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_03_02_02_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 5, 7, 12] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 3 + 5 + 7 + 12 = 27
      decide
    have hzsq : (∑ i, (((![3, 5, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 227 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 5^2 + 7^2 + 12^2 = 227
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_02_02_05
#print axioms Paper7MomentGapNumeric.valid_03_02_02_05

def qvalues_03_02_02_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 119, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_02_02_05

theorem row_03_02_02_05 : b4RowContribution (![3, 5, 7, 12] : Fin 4 → ℕ) = 119 := by
  calc
    b4RowContribution (![3, 5, 7, 12] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_03_02_02_05) :=
      sparseRow_sound (![3, 5, 7, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_03_02_02_05) valid_03_02_02_05
    _ = 119 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_02_02_05 Q := by
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
        _ = 119 := by decide
#print axioms Paper7MomentGapNumeric.row_03_02_02_05

theorem weighted_03_02_02_05 : b4RawGapContribution ![3, 2, 2, 5] = 2856 := by
  calc
    b4RawGapContribution ![3, 2, 2, 5] = b4GapPatternWeight 2 2 5 * 119 :=
      b4GapContribution_from_row 3 2 2 5 119 row_03_02_02_05
    _ = 2856 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_05

theorem row_03_02_02_06 : b4RowContribution (![3, 5, 7, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 7, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 7 + 13 = 28
    decide
  have hzsq : (∑ i, (((![3, 5, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 252 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 7^2 + 13^2 = 252
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_02_06

theorem weighted_03_02_02_06 : b4RawGapContribution ![3, 2, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 2, 6] = b4GapPatternWeight 2 2 6 * 0 :=
      b4GapContribution_from_row 3 2 2 6 0 row_03_02_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_06

def layers_03_02_02_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 21, 23, 23, 21, 18, 14, 10, 6, 3, 1, 0, 0, 0], ![1, 4, 10, 20, 34, 52, 73, 96, 119, 140, 158, 172, 182, 188, 191, 191, 188, 182, 172]]
#print axioms Paper7MomentGapNumeric.layers_03_02_02_07

theorem cells_03_02_02_07 : QTableValid (![3, 5, 7, 14] : Fin 4 → ℕ) layers_03_02_02_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_02_02_07

theorem valid_03_02_02_07 :
    SparseRowValid (![3, 5, 7, 14] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_03_02_02_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 5, 7, 14] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 3 + 5 + 7 + 14 = 29
      decide
    have hzsq : (∑ i, (((![3, 5, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 279 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 5^2 + 7^2 + 14^2 = 279
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_02_02_07
#print axioms Paper7MomentGapNumeric.valid_03_02_02_07

def qvalues_03_02_02_07 : Fin 19 → ℕ := ![0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_02_02_07

theorem row_03_02_02_07 : b4RowContribution (![3, 5, 7, 14] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![3, 5, 7, 14] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_03_02_02_07) :=
      sparseRow_sound (![3, 5, 7, 14] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_03_02_02_07) valid_03_02_02_07
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_02_02_07 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_03_02_02_07

theorem weighted_03_02_02_07 : b4RawGapContribution ![3, 2, 2, 7] = 480 := by
  calc
    b4RawGapContribution ![3, 2, 2, 7] = b4GapPatternWeight 2 2 7 * 20 :=
      b4GapContribution_from_row 3 2 2 7 20 row_03_02_02_07
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_07

theorem row_03_02_02_08 : b4RowContribution (![3, 5, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 7, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 7 + 15 = 30
    decide
  have hzsq : (∑ i, (((![3, 5, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 308 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 7^2 + 15^2 = 308
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_02_08

theorem weighted_03_02_02_08 : b4RawGapContribution ![3, 2, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 2, 8] = b4GapPatternWeight 2 2 8 * 0 :=
      b4GapContribution_from_row 3 2 2 8 0 row_03_02_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_08

theorem row_03_02_02_09 : b4RowContribution (![3, 5, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 7, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 7 + 16 = 31
    decide
  have hzsq : (∑ i, (((![3, 5, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 339 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 7^2 + 16^2 = 339
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_02_09

theorem weighted_03_02_02_09 : b4RawGapContribution ![3, 2, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 2, 9] = b4GapPatternWeight 2 2 9 * 0 :=
      b4GapContribution_from_row 3 2 2 9 0 row_03_02_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_09

theorem row_03_02_02_10 : b4RowContribution (![3, 5, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 7, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 7 + 17 = 32
    decide
  have hzsq : (∑ i, (((![3, 5, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 372 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 7^2 + 17^2 = 372
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_02_10

theorem weighted_03_02_02_10 : b4RawGapContribution ![3, 2, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 2, 10] = b4GapPatternWeight 2 2 10 * 0 :=
      b4GapContribution_from_row 3 2 2 10 0 row_03_02_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_10

theorem row_03_02_02_11 : b4RowContribution (![3, 5, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 7, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 7 + 18 = 33
    decide
  have hzsq : (∑ i, (((![3, 5, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 407 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 7^2 + 18^2 = 407
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_02_11

theorem weighted_03_02_02_11 : b4RawGapContribution ![3, 2, 2, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 2, 11] = b4GapPatternWeight 2 2 11 * 0 :=
      b4GapContribution_from_row 3 2 2 11 0 row_03_02_02_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_11

theorem row_03_02_02_12 : b4RowContribution (![3, 5, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 7, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 7 + 19 = 34
    decide
  have hzsq : (∑ i, (((![3, 5, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 444 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 7^2 + 19^2 = 444
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_02_12

theorem weighted_03_02_02_12 : b4RawGapContribution ![3, 2, 2, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 2, 12] = b4GapPatternWeight 2 2 12 * 0 :=
      b4GapContribution_from_row 3 2 2 12 0 row_03_02_02_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_12

theorem row_03_02_02_13 : b4RowContribution (![3, 5, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 7, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 7 + 20 = 35
    decide
  have hzsq : (∑ i, (((![3, 5, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 483 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 7^2 + 20^2 = 483
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_02_13

theorem weighted_03_02_02_13 : b4RawGapContribution ![3, 2, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 2, 13] = b4GapPatternWeight 2 2 13 * 0 :=
      b4GapContribution_from_row 3 2 2 13 0 row_03_02_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_13

theorem row_03_02_02_14 : b4RowContribution (![3, 5, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 7, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 7 + 21 = 36
    decide
  have hzsq : (∑ i, (((![3, 5, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 524 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 7^2 + 21^2 = 524
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_02_14

theorem weighted_03_02_02_14 : b4RawGapContribution ![3, 2, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 2, 14] = b4GapPatternWeight 2 2 14 * 0 :=
      b4GapContribution_from_row 3 2 2 14 0 row_03_02_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_14

theorem row_03_02_02_15 : b4RowContribution (![3, 5, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 7, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 7 + 22 = 37
    decide
  have hzsq : (∑ i, (((![3, 5, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 567 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 7^2 + 22^2 = 567
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_02_15

theorem weighted_03_02_02_15 : b4RawGapContribution ![3, 2, 2, 15] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 2, 15] = b4GapPatternWeight 2 2 15 * 0 :=
      b4GapContribution_from_row 3 2 2 15 0 row_03_02_02_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_02_15

def dvalues_03_02_02 : Fin 16 → ℕ := ![0, 0, 0, 0, 0, 2856, 0, 480, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_02_02

theorem dblock_03_02_02 : b4GapPatternDBlock 3 2 2 = 3336 := by
  calc
    b4GapPatternDBlock 3 2 2 = ∑ d : Fin 16, dvalues_03_02_02 d := by
      apply b4GapDBlock_of_rows 3 2 2 dvalues_03_02_02
      intro d
      fin_cases d
      · exact weighted_03_02_02_00
      · exact weighted_03_02_02_01
      · exact weighted_03_02_02_02
      · exact weighted_03_02_02_03
      · exact weighted_03_02_02_04
      · exact weighted_03_02_02_05
      · exact weighted_03_02_02_06
      · exact weighted_03_02_02_07
      · exact weighted_03_02_02_08
      · exact weighted_03_02_02_09
      · exact weighted_03_02_02_10
      · exact weighted_03_02_02_11
      · exact weighted_03_02_02_12
      · exact weighted_03_02_02_13
      · exact weighted_03_02_02_14
      · exact weighted_03_02_02_15
    _ = 3336 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_02_02

end Paper7MomentGapNumeric
