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

theorem row_03_00_02_00 : b4RowContribution (![3, 3, 5, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 5] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 5 = 16
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 68 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 5^2 = 68
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_00

theorem weighted_03_00_02_00 : b4RawGapContribution ![3, 0, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 0] = b4GapPatternWeight 0 2 0 * 0 :=
      b4GapContribution_from_row 3 0 2 0 0 row_03_00_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_00

theorem row_03_00_02_01 : b4RowContribution (![3, 3, 5, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 6] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 6 = 17
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 79 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 6^2 = 79
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_01

theorem weighted_03_00_02_01 : b4RawGapContribution ![3, 0, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 1] = b4GapPatternWeight 0 2 1 * 0 :=
      b4GapContribution_from_row 3 0 2 1 0 row_03_00_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_01

theorem row_03_00_02_02 : b4RowContribution (![3, 3, 5, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 7] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 7 = 18
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 92 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 7^2 = 92
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_02

theorem weighted_03_00_02_02 : b4RawGapContribution ![3, 0, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 2] = b4GapPatternWeight 0 2 2 * 0 :=
      b4GapContribution_from_row 3 0 2 2 0 row_03_00_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_02

theorem row_03_00_02_03 : b4RowContribution (![3, 3, 5, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 8] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 8 = 19
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 107 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 8^2 = 107
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_03

theorem weighted_03_00_02_03 : b4RawGapContribution ![3, 0, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 3] = b4GapPatternWeight 0 2 3 * 0 :=
      b4GapContribution_from_row 3 0 2 3 0 row_03_00_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_03

theorem row_03_00_02_04 : b4RowContribution (![3, 3, 5, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 9] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 9 = 20
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 124 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 9^2 = 124
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_04

theorem weighted_03_00_02_04 : b4RawGapContribution ![3, 0, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 4] = b4GapPatternWeight 0 2 4 * 0 :=
      b4GapContribution_from_row 3 0 2 4 0 row_03_00_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_04

theorem row_03_00_02_05 : b4RowContribution (![3, 3, 5, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 10] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 10 = 21
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 143 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 10^2 = 143
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_05

theorem weighted_03_00_02_05 : b4RawGapContribution ![3, 0, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 5] = b4GapPatternWeight 0 2 5 * 0 :=
      b4GapContribution_from_row 3 0 2 5 0 row_03_00_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_05

theorem row_03_00_02_06 : b4RowContribution (![3, 3, 5, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 11] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 11 = 22
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 164 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 11^2 = 164
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_06

theorem weighted_03_00_02_06 : b4RawGapContribution ![3, 0, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 6] = b4GapPatternWeight 0 2 6 * 0 :=
      b4GapContribution_from_row 3 0 2 6 0 row_03_00_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_06

theorem row_03_00_02_07 : b4RowContribution (![3, 3, 5, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 12] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 12 = 23
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 187 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 12^2 = 187
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_07

theorem weighted_03_00_02_07 : b4RawGapContribution ![3, 0, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 7] = b4GapPatternWeight 0 2 7 * 0 :=
      b4GapContribution_from_row 3 0 2 7 0 row_03_00_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_07

theorem row_03_00_02_08 : b4RowContribution (![3, 3, 5, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 13] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 13 = 24
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 212 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 13^2 = 212
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_08

theorem weighted_03_00_02_08 : b4RawGapContribution ![3, 0, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 8] = b4GapPatternWeight 0 2 8 * 0 :=
      b4GapContribution_from_row 3 0 2 8 0 row_03_00_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_08

def layers_03_00_02_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 15, 15, 13, 10, 6, 3, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 4, 10, 20, 33, 48, 63, 76, 86, 92, 95, 96, 96, 96, 96, 95, 92, 86, 76]]
#print axioms Paper7MomentGapNumeric.layers_03_00_02_09

theorem cells_03_00_02_09 : QTableValid (![3, 3, 5, 14] : Fin 4 → ℕ) layers_03_00_02_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_00_02_09

theorem valid_03_00_02_09 :
    SparseRowValid (![3, 3, 5, 14] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_00_02_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 3, 5, 14] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 3 + 3 + 5 + 14 = 25
      decide
    have hzsq : (∑ i, (((![3, 3, 5, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 239 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 3^2 + 5^2 + 14^2 = 239
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_00_02_09
#print axioms Paper7MomentGapNumeric.valid_03_00_02_09

def qvalues_03_00_02_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_00_02_09

theorem row_03_00_02_09 : b4RowContribution (![3, 3, 5, 14] : Fin 4 → ℕ) = 48 := by
  calc
    b4RowContribution (![3, 3, 5, 14] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_03_00_02_09) :=
      sparseRow_sound (![3, 3, 5, 14] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_00_02_09) valid_03_00_02_09
    _ = 48 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_00_02_09 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.row_03_00_02_09

theorem weighted_03_00_02_09 : b4RawGapContribution ![3, 0, 2, 9] = 576 := by
  calc
    b4RawGapContribution ![3, 0, 2, 9] = b4GapPatternWeight 0 2 9 * 48 :=
      b4GapContribution_from_row 3 0 2 9 48 row_03_00_02_09
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_09

theorem row_03_00_02_10 : b4RowContribution (![3, 3, 5, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 15] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 15 = 26
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 268 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 15^2 = 268
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_10

theorem weighted_03_00_02_10 : b4RawGapContribution ![3, 0, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 10] = b4GapPatternWeight 0 2 10 * 0 :=
      b4GapContribution_from_row 3 0 2 10 0 row_03_00_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_10

theorem row_03_00_02_11 : b4RowContribution (![3, 3, 5, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 16] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 16 = 27
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 299 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 16^2 = 299
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_11

theorem weighted_03_00_02_11 : b4RawGapContribution ![3, 0, 2, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 11] = b4GapPatternWeight 0 2 11 * 0 :=
      b4GapContribution_from_row 3 0 2 11 0 row_03_00_02_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_11

theorem row_03_00_02_12 : b4RowContribution (![3, 3, 5, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 17] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 17 = 28
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 332 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 17^2 = 332
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_12

theorem weighted_03_00_02_12 : b4RawGapContribution ![3, 0, 2, 12] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 12] = b4GapPatternWeight 0 2 12 * 0 :=
      b4GapContribution_from_row 3 0 2 12 0 row_03_00_02_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_12

theorem row_03_00_02_13 : b4RowContribution (![3, 3, 5, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 18] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 18 = 29
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 367 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 18^2 = 367
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_13

theorem weighted_03_00_02_13 : b4RawGapContribution ![3, 0, 2, 13] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 13] = b4GapPatternWeight 0 2 13 * 0 :=
      b4GapContribution_from_row 3 0 2 13 0 row_03_00_02_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_13

theorem row_03_00_02_14 : b4RowContribution (![3, 3, 5, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 19] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 19 = 30
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 404 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 19^2 = 404
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_14

theorem weighted_03_00_02_14 : b4RawGapContribution ![3, 0, 2, 14] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 14] = b4GapPatternWeight 0 2 14 * 0 :=
      b4GapContribution_from_row 3 0 2 14 0 row_03_00_02_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_14

theorem row_03_00_02_15 : b4RowContribution (![3, 3, 5, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 20] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 20 = 31
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 443 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 20^2 = 443
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_15

theorem weighted_03_00_02_15 : b4RawGapContribution ![3, 0, 2, 15] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 15] = b4GapPatternWeight 0 2 15 * 0 :=
      b4GapContribution_from_row 3 0 2 15 0 row_03_00_02_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_15

theorem row_03_00_02_16 : b4RowContribution (![3, 3, 5, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 21] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 21 = 32
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 484 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 21^2 = 484
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_16

theorem weighted_03_00_02_16 : b4RawGapContribution ![3, 0, 2, 16] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 16] = b4GapPatternWeight 0 2 16 * 0 :=
      b4GapContribution_from_row 3 0 2 16 0 row_03_00_02_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_16

theorem row_03_00_02_17 : b4RowContribution (![3, 3, 5, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 22] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 22 = 33
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 527 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 22^2 = 527
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_17

theorem weighted_03_00_02_17 : b4RawGapContribution ![3, 0, 2, 17] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 17] = b4GapPatternWeight 0 2 17 * 0 :=
      b4GapContribution_from_row 3 0 2 17 0 row_03_00_02_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_17

theorem row_03_00_02_18 : b4RowContribution (![3, 3, 5, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 23] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 23 = 34
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 572 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 23^2 = 572
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_18

theorem weighted_03_00_02_18 : b4RawGapContribution ![3, 0, 2, 18] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 18] = b4GapPatternWeight 0 2 18 * 0 :=
      b4GapContribution_from_row 3 0 2 18 0 row_03_00_02_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_18

theorem row_03_00_02_19 : b4RowContribution (![3, 3, 5, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 24] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 24 = 35
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 619 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 24^2 = 619
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_19

theorem weighted_03_00_02_19 : b4RawGapContribution ![3, 0, 2, 19] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 19] = b4GapPatternWeight 0 2 19 * 0 :=
      b4GapContribution_from_row 3 0 2 19 0 row_03_00_02_19
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_19

theorem row_03_00_02_20 : b4RowContribution (![3, 3, 5, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 25] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 25 = 36
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 668 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 25^2 = 668
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_20

theorem weighted_03_00_02_20 : b4RawGapContribution ![3, 0, 2, 20] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 20] = b4GapPatternWeight 0 2 20 * 0 :=
      b4GapContribution_from_row 3 0 2 20 0 row_03_00_02_20
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_20

theorem row_03_00_02_21 : b4RowContribution (![3, 3, 5, 26] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 5, 26] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 5 + 26 = 37
    decide
  have hzsq : (∑ i, (((![3, 3, 5, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 719 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 5^2 + 26^2 = 719
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_02_21

theorem weighted_03_00_02_21 : b4RawGapContribution ![3, 0, 2, 21] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 2, 21] = b4GapPatternWeight 0 2 21 * 0 :=
      b4GapContribution_from_row 3 0 2 21 0 row_03_00_02_21
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_02_21

def dvalues_03_00_02 : Fin 22 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_00_02

theorem dblock_03_00_02 : b4GapPatternDBlock 3 0 2 = 576 := by
  calc
    b4GapPatternDBlock 3 0 2 = ∑ d : Fin 22, dvalues_03_00_02 d := by
      apply b4GapDBlock_of_rows 3 0 2 dvalues_03_00_02
      intro d
      fin_cases d
      · exact weighted_03_00_02_00
      · exact weighted_03_00_02_01
      · exact weighted_03_00_02_02
      · exact weighted_03_00_02_03
      · exact weighted_03_00_02_04
      · exact weighted_03_00_02_05
      · exact weighted_03_00_02_06
      · exact weighted_03_00_02_07
      · exact weighted_03_00_02_08
      · exact weighted_03_00_02_09
      · exact weighted_03_00_02_10
      · exact weighted_03_00_02_11
      · exact weighted_03_00_02_12
      · exact weighted_03_00_02_13
      · exact weighted_03_00_02_14
      · exact weighted_03_00_02_15
      · exact weighted_03_00_02_16
      · exact weighted_03_00_02_17
      · exact weighted_03_00_02_18
      · exact weighted_03_00_02_19
      · exact weighted_03_00_02_20
      · exact weighted_03_00_02_21
    _ = 576 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_00_02

end Paper7MomentGapNumeric
