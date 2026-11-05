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

theorem row_00_05_00_00 : b4RowContribution (![0, 5, 5, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 5] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 5 = 15
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 75 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 5^2 = 75
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_00

theorem weighted_00_05_00_00 : b4RawGapContribution ![0, 5, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 0] = b4GapPatternWeight 5 0 0 * 0 :=
      b4GapContribution_from_row 0 5 0 0 0 row_00_05_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_00

theorem row_00_05_00_01 : b4RowContribution (![0, 5, 5, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 6] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 6 = 16
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 86 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 6^2 = 86
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_01

theorem weighted_00_05_00_01 : b4RawGapContribution ![0, 5, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 1] = b4GapPatternWeight 5 0 1 * 0 :=
      b4GapContribution_from_row 0 5 0 1 0 row_00_05_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_01

theorem row_00_05_00_02 : b4RowContribution (![0, 5, 5, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 7] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 7 = 17
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 99 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 7^2 = 99
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_02

theorem weighted_00_05_00_02 : b4RawGapContribution ![0, 5, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 2] = b4GapPatternWeight 5 0 2 * 0 :=
      b4GapContribution_from_row 0 5 0 2 0 row_00_05_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_02

theorem row_00_05_00_03 : b4RowContribution (![0, 5, 5, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 8] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 8 = 18
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 114 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 8^2 = 114
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_03

theorem weighted_00_05_00_03 : b4RawGapContribution ![0, 5, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 3] = b4GapPatternWeight 5 0 3 * 0 :=
      b4GapContribution_from_row 0 5 0 3 0 row_00_05_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_03

theorem row_00_05_00_04 : b4RowContribution (![0, 5, 5, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 9] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 9 = 19
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 131 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 9^2 = 131
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_04

theorem weighted_00_05_00_04 : b4RawGapContribution ![0, 5, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 4] = b4GapPatternWeight 5 0 4 * 0 :=
      b4GapContribution_from_row 0 5 0 4 0 row_00_05_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_04

theorem row_00_05_00_05 : b4RowContribution (![0, 5, 5, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 10] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 10 = 20
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 150 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 10^2 = 150
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_05

theorem weighted_00_05_00_05 : b4RawGapContribution ![0, 5, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 5] = b4GapPatternWeight 5 0 5 * 0 :=
      b4GapContribution_from_row 0 5 0 5 0 row_00_05_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_05

theorem row_00_05_00_06 : b4RowContribution (![0, 5, 5, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 11] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 11 = 21
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 171 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 11^2 = 171
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_06

theorem weighted_00_05_00_06 : b4RawGapContribution ![0, 5, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 6] = b4GapPatternWeight 5 0 6 * 0 :=
      b4GapContribution_from_row 0 5 0 6 0 row_00_05_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_06

theorem row_00_05_00_07 : b4RowContribution (![0, 5, 5, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 12] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 12 = 22
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 194 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 12^2 = 194
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_07

theorem weighted_00_05_00_07 : b4RawGapContribution ![0, 5, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 7] = b4GapPatternWeight 5 0 7 * 0 :=
      b4GapContribution_from_row 0 5 0 7 0 row_00_05_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_07

def layers_00_05_00_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 26, 30, 33, 35, 36, 36, 36, 36, 35, 33, 30, 26, 21]]
#print axioms Paper7MomentGapNumeric.layers_00_05_00_08

theorem cells_00_05_00_08 : QTableValid (![0, 5, 5, 13] : Fin 4 → ℕ) layers_00_05_00_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_05_00_08

theorem valid_00_05_00_08 :
    SparseRowValid (![0, 5, 5, 13] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_05_00_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 5, 5, 13] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 0 + 5 + 5 + 13 = 23
      decide
    have hzsq : (∑ i, (((![0, 5, 5, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 219 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 5^2 + 5^2 + 13^2 = 219
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_05_00_08
#print axioms Paper7MomentGapNumeric.valid_00_05_00_08

def qvalues_00_05_00_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_05_00_08

theorem row_00_05_00_08 : b4RowContribution (![0, 5, 5, 13] : Fin 4 → ℕ) = 36 := by
  calc
    b4RowContribution (![0, 5, 5, 13] : Fin 4 → ℕ) =
        sparseRowValue ({12} : Finset (Fin 19)) (fun _ => layers_00_05_00_08) :=
      sparseRow_sound (![0, 5, 5, 13] : Fin 4 → ℕ) ({12} : Finset (Fin 19)) (fun _ => layers_00_05_00_08) valid_00_05_00_08
    _ = 36 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_05_00_08 Q := by
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
        _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.row_00_05_00_08

theorem weighted_00_05_00_08 : b4RawGapContribution ![0, 5, 0, 8] = 432 := by
  calc
    b4RawGapContribution ![0, 5, 0, 8] = b4GapPatternWeight 5 0 8 * 36 :=
      b4GapContribution_from_row 0 5 0 8 36 row_00_05_00_08
    _ = 432 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_08

theorem row_00_05_00_09 : b4RowContribution (![0, 5, 5, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 14] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 14 = 24
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 246 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 14^2 = 246
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_09

theorem weighted_00_05_00_09 : b4RawGapContribution ![0, 5, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 9] = b4GapPatternWeight 5 0 9 * 0 :=
      b4GapContribution_from_row 0 5 0 9 0 row_00_05_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_09

def layers_00_05_00_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 26, 30, 33, 35, 36, 36, 36, 36, 36, 36, 35, 33, 30]]
#print axioms Paper7MomentGapNumeric.layers_00_05_00_10

theorem cells_00_05_00_10 : QTableValid (![0, 5, 5, 15] : Fin 4 → ℕ) layers_00_05_00_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_05_00_10

theorem valid_00_05_00_10 :
    SparseRowValid (![0, 5, 5, 15] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_05_00_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 5, 5, 15] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 5 + 5 + 15 = 25
      decide
    have hzsq : (∑ i, (((![0, 5, 5, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 275 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 5^2 + 5^2 + 15^2 = 275
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_05_00_10
#print axioms Paper7MomentGapNumeric.valid_00_05_00_10

def qvalues_00_05_00_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_05_00_10

theorem row_00_05_00_10 : b4RowContribution (![0, 5, 5, 15] : Fin 4 → ℕ) = 36 := by
  calc
    b4RowContribution (![0, 5, 5, 15] : Fin 4 → ℕ) =
        sparseRowValue ({11} : Finset (Fin 19)) (fun _ => layers_00_05_00_10) :=
      sparseRow_sound (![0, 5, 5, 15] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_05_00_10) valid_00_05_00_10
    _ = 36 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_05_00_10 Q := by
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
        _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.row_00_05_00_10

theorem weighted_00_05_00_10 : b4RawGapContribution ![0, 5, 0, 10] = 432 := by
  calc
    b4RawGapContribution ![0, 5, 0, 10] = b4GapPatternWeight 5 0 10 * 36 :=
      b4GapContribution_from_row 0 5 0 10 36 row_00_05_00_10
    _ = 432 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_10

theorem row_00_05_00_11 : b4RowContribution (![0, 5, 5, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 16] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 16 = 26
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 16^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_11

theorem weighted_00_05_00_11 : b4RawGapContribution ![0, 5, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 11] = b4GapPatternWeight 5 0 11 * 0 :=
      b4GapContribution_from_row 0 5 0 11 0 row_00_05_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_11

theorem row_00_05_00_12 : b4RowContribution (![0, 5, 5, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 17] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 17 = 27
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 339 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 17^2 = 339
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_12

theorem weighted_00_05_00_12 : b4RawGapContribution ![0, 5, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 12] = b4GapPatternWeight 5 0 12 * 0 :=
      b4GapContribution_from_row 0 5 0 12 0 row_00_05_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_12

theorem row_00_05_00_13 : b4RowContribution (![0, 5, 5, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 18] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 18 = 28
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 374 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 18^2 = 374
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_13

theorem weighted_00_05_00_13 : b4RawGapContribution ![0, 5, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 13] = b4GapPatternWeight 5 0 13 * 0 :=
      b4GapContribution_from_row 0 5 0 13 0 row_00_05_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_13

theorem row_00_05_00_14 : b4RowContribution (![0, 5, 5, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 19] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 19 = 29
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 411 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 19^2 = 411
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_14

theorem weighted_00_05_00_14 : b4RawGapContribution ![0, 5, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 14] = b4GapPatternWeight 5 0 14 * 0 :=
      b4GapContribution_from_row 0 5 0 14 0 row_00_05_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_14

theorem row_00_05_00_15 : b4RowContribution (![0, 5, 5, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 20] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 20 = 30
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 20^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_15

theorem weighted_00_05_00_15 : b4RawGapContribution ![0, 5, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 15] = b4GapPatternWeight 5 0 15 * 0 :=
      b4GapContribution_from_row 0 5 0 15 0 row_00_05_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_15

theorem row_00_05_00_16 : b4RowContribution (![0, 5, 5, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 21] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 21 = 31
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 491 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 21^2 = 491
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_16

theorem weighted_00_05_00_16 : b4RawGapContribution ![0, 5, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 16] = b4GapPatternWeight 5 0 16 * 0 :=
      b4GapContribution_from_row 0 5 0 16 0 row_00_05_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_16

theorem row_00_05_00_17 : b4RowContribution (![0, 5, 5, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 22] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 22 = 32
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 534 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 22^2 = 534
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_17

theorem weighted_00_05_00_17 : b4RawGapContribution ![0, 5, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 17] = b4GapPatternWeight 5 0 17 * 0 :=
      b4GapContribution_from_row 0 5 0 17 0 row_00_05_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_17

theorem row_00_05_00_18 : b4RowContribution (![0, 5, 5, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 23] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 23 = 33
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 579 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 23^2 = 579
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_18

theorem weighted_00_05_00_18 : b4RawGapContribution ![0, 5, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 18] = b4GapPatternWeight 5 0 18 * 0 :=
      b4GapContribution_from_row 0 5 0 18 0 row_00_05_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_18

theorem row_00_05_00_19 : b4RowContribution (![0, 5, 5, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 24] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 24 = 34
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 626 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 24^2 = 626
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_19

theorem weighted_00_05_00_19 : b4RawGapContribution ![0, 5, 0, 19] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 19] = b4GapPatternWeight 5 0 19 * 0 :=
      b4GapContribution_from_row 0 5 0 19 0 row_00_05_00_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_19

theorem row_00_05_00_20 : b4RowContribution (![0, 5, 5, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 25] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 25 = 35
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 675 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 25^2 = 675
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_20

theorem weighted_00_05_00_20 : b4RawGapContribution ![0, 5, 0, 20] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 20] = b4GapPatternWeight 5 0 20 * 0 :=
      b4GapContribution_from_row 0 5 0 20 0 row_00_05_00_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_20

theorem row_00_05_00_21 : b4RowContribution (![0, 5, 5, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 26] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 26 = 36
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 726 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 26^2 = 726
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_21

theorem weighted_00_05_00_21 : b4RawGapContribution ![0, 5, 0, 21] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 21] = b4GapPatternWeight 5 0 21 * 0 :=
      b4GapContribution_from_row 0 5 0 21 0 row_00_05_00_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_21

theorem row_00_05_00_22 : b4RowContribution (![0, 5, 5, 27] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 5, 27] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 5 + 27 = 37
    decide
  have hzsq : (∑ i, (((![0, 5, 5, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 779 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 5^2 + 27^2 = 779
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_00_22

theorem weighted_00_05_00_22 : b4RawGapContribution ![0, 5, 0, 22] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 0, 22] = b4GapPatternWeight 5 0 22 * 0 :=
      b4GapContribution_from_row 0 5 0 22 0 row_00_05_00_22
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_00_22

def dvalues_00_05_00 : Fin 23 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 432, 0, 432, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_05_00

theorem dblock_00_05_00 : b4GapPatternDBlock 0 5 0 = 864 := by
  calc
    b4GapPatternDBlock 0 5 0 = ∑ d : Fin 23, dvalues_00_05_00 d := by
      apply b4GapDBlock_of_rows 0 5 0 dvalues_00_05_00
      intro d
      fin_cases d
      · exact weighted_00_05_00_00
      · exact weighted_00_05_00_01
      · exact weighted_00_05_00_02
      · exact weighted_00_05_00_03
      · exact weighted_00_05_00_04
      · exact weighted_00_05_00_05
      · exact weighted_00_05_00_06
      · exact weighted_00_05_00_07
      · exact weighted_00_05_00_08
      · exact weighted_00_05_00_09
      · exact weighted_00_05_00_10
      · exact weighted_00_05_00_11
      · exact weighted_00_05_00_12
      · exact weighted_00_05_00_13
      · exact weighted_00_05_00_14
      · exact weighted_00_05_00_15
      · exact weighted_00_05_00_16
      · exact weighted_00_05_00_17
      · exact weighted_00_05_00_18
      · exact weighted_00_05_00_19
      · exact weighted_00_05_00_20
      · exact weighted_00_05_00_21
      · exact weighted_00_05_00_22
    _ = 864 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_05_00

end Paper7MomentGapNumeric
