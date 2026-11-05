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

theorem row_02_04_00_00 : b4RowContribution (![2, 6, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 6] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 6 = 20
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 112 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 6^2 = 112
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_00

theorem weighted_02_04_00_00 : b4RawGapContribution ![2, 4, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 0] = b4GapPatternWeight 4 0 0 * 0 :=
      b4GapContribution_from_row 2 4 0 0 0 row_02_04_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_00

theorem row_02_04_00_01 : b4RowContribution (![2, 6, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 7] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 7 = 21
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 125 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 7^2 = 125
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_01

theorem weighted_02_04_00_01 : b4RawGapContribution ![2, 4, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 1] = b4GapPatternWeight 4 0 1 * 0 :=
      b4GapContribution_from_row 2 4 0 1 0 row_02_04_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_01

theorem row_02_04_00_02 : b4RowContribution (![2, 6, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 8] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 8 = 22
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 140 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 8^2 = 140
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_02

theorem weighted_02_04_00_02 : b4RawGapContribution ![2, 4, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 2] = b4GapPatternWeight 4 0 2 * 0 :=
      b4GapContribution_from_row 2 4 0 2 0 row_02_04_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_02

theorem row_02_04_00_03 : b4RowContribution (![2, 6, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 9] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 9 = 23
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 157 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 9^2 = 157
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_03

theorem weighted_02_04_00_03 : b4RawGapContribution ![2, 4, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 3] = b4GapPatternWeight 4 0 3 * 0 :=
      b4GapContribution_from_row 2 4 0 3 0 row_02_04_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_03

theorem row_02_04_00_04 : b4RowContribution (![2, 6, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 10] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 10 = 24
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 176 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 10^2 = 176
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_04

theorem weighted_02_04_00_04 : b4RawGapContribution ![2, 4, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 4] = b4GapPatternWeight 4 0 4 * 0 :=
      b4GapContribution_from_row 2 4 0 4 0 row_02_04_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_04

theorem row_02_04_00_05 : b4RowContribution (![2, 6, 6, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 11] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 11 = 25
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 197 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 11^2 = 197
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_05

theorem weighted_02_04_00_05 : b4RawGapContribution ![2, 4, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 5] = b4GapPatternWeight 4 0 5 * 0 :=
      b4GapContribution_from_row 2 4 0 5 0 row_02_04_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_05

theorem row_02_04_00_06 : b4RowContribution (![2, 6, 6, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 12] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 12 = 26
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 220 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 12^2 = 220
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_06

theorem weighted_02_04_00_06 : b4RawGapContribution ![2, 4, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 6] = b4GapPatternWeight 4 0 6 * 0 :=
      b4GapContribution_from_row 2 4 0 6 0 row_02_04_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_06

theorem row_02_04_00_07 : b4RowContribution (![2, 6, 6, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 13 = 27
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 245 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 13^2 = 245
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_07

theorem weighted_02_04_00_07 : b4RawGapContribution ![2, 4, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 7] = b4GapPatternWeight 4 0 7 * 0 :=
      b4GapContribution_from_row 2 4 0 7 0 row_02_04_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_07

def layers_02_04_00_08 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 19, 18, 15, 12, 9, 6, 3, 1, 0, 0, 0, 0], ![1, 4, 10, 19, 31, 46, 64, 83, 101, 116, 128, 137, 143, 146, 147, 146, 143, 137, 128]]
#print axioms Paper7MomentGapNumeric.layers_02_04_00_08

theorem cells_02_04_00_08 : QTableValid (![2, 6, 6, 14] : Fin 4 → ℕ) layers_02_04_00_08 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_04_00_08

theorem valid_02_04_00_08 :
    SparseRowValid (![2, 6, 6, 14] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_02_04_00_08) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 6, 6, 14] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 2 + 6 + 6 + 14 = 28
      decide
    have hzsq : (∑ i, (((![2, 6, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 272 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 6^2 + 6^2 + 14^2 = 272
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_04_00_08
#print axioms Paper7MomentGapNumeric.valid_02_04_00_08

def qvalues_02_04_00_08 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_04_00_08

theorem row_02_04_00_08 : b4RowContribution (![2, 6, 6, 14] : Fin 4 → ℕ) = 101 := by
  calc
    b4RowContribution (![2, 6, 6, 14] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_02_04_00_08) :=
      sparseRow_sound (![2, 6, 6, 14] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_02_04_00_08) valid_02_04_00_08
    _ = 101 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_04_00_08 Q := by
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
        _ = 101 := by decide
#print axioms Paper7MomentGapNumeric.row_02_04_00_08

theorem weighted_02_04_00_08 : b4RawGapContribution ![2, 4, 0, 8] = 1212 := by
  calc
    b4RawGapContribution ![2, 4, 0, 8] = b4GapPatternWeight 4 0 8 * 101 :=
      b4GapContribution_from_row 2 4 0 8 101 row_02_04_00_08
    _ = 1212 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_08

theorem row_02_04_00_09 : b4RowContribution (![2, 6, 6, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 15 = 29
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 301 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 15^2 = 301
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_09

theorem weighted_02_04_00_09 : b4RawGapContribution ![2, 4, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 9] = b4GapPatternWeight 4 0 9 * 0 :=
      b4GapContribution_from_row 2 4 0 9 0 row_02_04_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_09

theorem row_02_04_00_10 : b4RowContribution (![2, 6, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 16 = 30
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 332 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 16^2 = 332
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_10

theorem weighted_02_04_00_10 : b4RawGapContribution ![2, 4, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 10] = b4GapPatternWeight 4 0 10 * 0 :=
      b4GapContribution_from_row 2 4 0 10 0 row_02_04_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_10

theorem row_02_04_00_11 : b4RowContribution (![2, 6, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 17 = 31
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 365 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 17^2 = 365
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_11

theorem weighted_02_04_00_11 : b4RawGapContribution ![2, 4, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 11] = b4GapPatternWeight 4 0 11 * 0 :=
      b4GapContribution_from_row 2 4 0 11 0 row_02_04_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_11

theorem row_02_04_00_12 : b4RowContribution (![2, 6, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 18 = 32
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 400 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 18^2 = 400
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_12

theorem weighted_02_04_00_12 : b4RawGapContribution ![2, 4, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 12] = b4GapPatternWeight 4 0 12 * 0 :=
      b4GapContribution_from_row 2 4 0 12 0 row_02_04_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_12

theorem row_02_04_00_13 : b4RowContribution (![2, 6, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 19 = 33
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 437 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 19^2 = 437
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_13

theorem weighted_02_04_00_13 : b4RawGapContribution ![2, 4, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 13] = b4GapPatternWeight 4 0 13 * 0 :=
      b4GapContribution_from_row 2 4 0 13 0 row_02_04_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_13

theorem row_02_04_00_14 : b4RowContribution (![2, 6, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 20 = 34
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 476 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 20^2 = 476
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_14

theorem weighted_02_04_00_14 : b4RawGapContribution ![2, 4, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 14] = b4GapPatternWeight 4 0 14 * 0 :=
      b4GapContribution_from_row 2 4 0 14 0 row_02_04_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_14

theorem row_02_04_00_15 : b4RowContribution (![2, 6, 6, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 21 = 35
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 517 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 21^2 = 517
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_15

theorem weighted_02_04_00_15 : b4RawGapContribution ![2, 4, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 15] = b4GapPatternWeight 4 0 15 * 0 :=
      b4GapContribution_from_row 2 4 0 15 0 row_02_04_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_15

theorem row_02_04_00_16 : b4RowContribution (![2, 6, 6, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 22 = 36
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 560 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 22^2 = 560
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_16

theorem weighted_02_04_00_16 : b4RawGapContribution ![2, 4, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 16] = b4GapPatternWeight 4 0 16 * 0 :=
      b4GapContribution_from_row 2 4 0 16 0 row_02_04_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_16

theorem row_02_04_00_17 : b4RowContribution (![2, 6, 6, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 6, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 6 + 23 = 37
    decide
  have hzsq : (∑ i, (((![2, 6, 6, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 605 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 6^2 + 23^2 = 605
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_00_17

theorem weighted_02_04_00_17 : b4RawGapContribution ![2, 4, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 0, 17] = b4GapPatternWeight 4 0 17 * 0 :=
      b4GapContribution_from_row 2 4 0 17 0 row_02_04_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_00_17

def dvalues_02_04_00 : Fin 18 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 1212, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_04_00

theorem dblock_02_04_00 : b4GapPatternDBlock 2 4 0 = 1212 := by
  calc
    b4GapPatternDBlock 2 4 0 = ∑ d : Fin 18, dvalues_02_04_00 d := by
      apply b4GapDBlock_of_rows 2 4 0 dvalues_02_04_00
      intro d
      fin_cases d
      · exact weighted_02_04_00_00
      · exact weighted_02_04_00_01
      · exact weighted_02_04_00_02
      · exact weighted_02_04_00_03
      · exact weighted_02_04_00_04
      · exact weighted_02_04_00_05
      · exact weighted_02_04_00_06
      · exact weighted_02_04_00_07
      · exact weighted_02_04_00_08
      · exact weighted_02_04_00_09
      · exact weighted_02_04_00_10
      · exact weighted_02_04_00_11
      · exact weighted_02_04_00_12
      · exact weighted_02_04_00_13
      · exact weighted_02_04_00_14
      · exact weighted_02_04_00_15
      · exact weighted_02_04_00_16
      · exact weighted_02_04_00_17
    _ = 1212 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_04_00

end Paper7MomentGapNumeric
