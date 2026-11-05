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

theorem row_01_03_03_00 : b4RowContribution (![1, 4, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 7] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 7 = 19
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 115 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 7^2 = 115
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_00

theorem weighted_01_03_03_00 : b4RawGapContribution ![1, 3, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 0] = b4GapPatternWeight 3 3 0 * 0 :=
      b4GapContribution_from_row 1 3 3 0 0 row_01_03_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_00

theorem row_01_03_03_01 : b4RowContribution (![1, 4, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 8] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 8 = 20
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 130 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 8^2 = 130
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_01

theorem weighted_01_03_03_01 : b4RawGapContribution ![1, 3, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 1] = b4GapPatternWeight 3 3 1 * 0 :=
      b4GapContribution_from_row 1 3 3 1 0 row_01_03_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_01

theorem row_01_03_03_02 : b4RowContribution (![1, 4, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 9] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 9 = 21
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 147 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 9^2 = 147
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_02

theorem weighted_01_03_03_02 : b4RawGapContribution ![1, 3, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 2] = b4GapPatternWeight 3 3 2 * 0 :=
      b4GapContribution_from_row 1 3 3 2 0 row_01_03_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_02

theorem row_01_03_03_03 : b4RowContribution (![1, 4, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 10] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 10 = 22
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 166 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 10^2 = 166
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_03

theorem weighted_01_03_03_03 : b4RawGapContribution ![1, 3, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 3] = b4GapPatternWeight 3 3 3 * 0 :=
      b4GapContribution_from_row 1 3 3 3 0 row_01_03_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_03

theorem row_01_03_03_04 : b4RowContribution (![1, 4, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 11] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 11 = 23
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 187 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 11^2 = 187
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_04

theorem weighted_01_03_03_04 : b4RawGapContribution ![1, 3, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 4] = b4GapPatternWeight 3 3 4 * 0 :=
      b4GapContribution_from_row 1 3 3 4 0 row_01_03_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_04

theorem row_01_03_03_05 : b4RowContribution (![1, 4, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 12] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 12 = 24
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 210 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 12^2 = 210
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_05

theorem weighted_01_03_03_05 : b4RawGapContribution ![1, 3, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 5] = b4GapPatternWeight 3 3 5 * 0 :=
      b4GapContribution_from_row 1 3 3 5 0 row_01_03_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_05

def layers_01_03_03_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 10, 10, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 35, 45, 55, 64, 71, 76, 79, 80, 80, 79, 76, 71, 64, 55]]
#print axioms Paper7MomentGapNumeric.layers_01_03_03_06

theorem cells_01_03_03_06 : QTableValid (![1, 4, 7, 13] : Fin 4 → ℕ) layers_01_03_03_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_03_06

theorem valid_01_03_03_06 :
    SparseRowValid (![1, 4, 7, 13] : Fin 4 → ℕ) ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_03_03_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 7, 13] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 7 + 13 = 25
      decide
    have hzsq : (∑ i, (((![1, 4, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 235 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 7^2 + 13^2 = 235
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_03_06
#print axioms Paper7MomentGapNumeric.valid_01_03_03_06

def qvalues_01_03_03_06 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_03_06

theorem row_01_03_03_06 : b4RowContribution (![1, 4, 7, 13] : Fin 4 → ℕ) = 59 := by
  calc
    b4RowContribution (![1, 4, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_03_03_06) :=
      sparseRow_sound (![1, 4, 7, 13] : Fin 4 → ℕ) ({1, 7} : Finset (Fin 19)) (fun _ => layers_01_03_03_06) valid_01_03_03_06
    _ = 59 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_03_06 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 59 := by decide
#print axioms Paper7MomentGapNumeric.row_01_03_03_06

theorem weighted_01_03_03_06 : b4RawGapContribution ![1, 3, 3, 6] = 1416 := by
  calc
    b4RawGapContribution ![1, 3, 3, 6] = b4GapPatternWeight 3 3 6 * 59 :=
      b4GapContribution_from_row 1 3 3 6 59 row_01_03_03_06
    _ = 1416 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_06

theorem row_01_03_03_07 : b4RowContribution (![1, 4, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 14] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 14 = 26
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 262 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 14^2 = 262
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_07

theorem weighted_01_03_03_07 : b4RawGapContribution ![1, 3, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 7] = b4GapPatternWeight 3 3 7 * 0 :=
      b4GapContribution_from_row 1 3 3 7 0 row_01_03_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_07

theorem row_01_03_03_08 : b4RowContribution (![1, 4, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 15] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 15 = 27
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 291 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 15^2 = 291
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_08

theorem weighted_01_03_03_08 : b4RawGapContribution ![1, 3, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 8] = b4GapPatternWeight 3 3 8 * 0 :=
      b4GapContribution_from_row 1 3 3 8 0 row_01_03_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_08

theorem row_01_03_03_09 : b4RowContribution (![1, 4, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 16] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 16 = 28
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 322 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 16^2 = 322
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_09

theorem weighted_01_03_03_09 : b4RawGapContribution ![1, 3, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 9] = b4GapPatternWeight 3 3 9 * 0 :=
      b4GapContribution_from_row 1 3 3 9 0 row_01_03_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_09

theorem row_01_03_03_10 : b4RowContribution (![1, 4, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 17] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 17 = 29
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 355 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 17^2 = 355
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_10

theorem weighted_01_03_03_10 : b4RawGapContribution ![1, 3, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 10] = b4GapPatternWeight 3 3 10 * 0 :=
      b4GapContribution_from_row 1 3 3 10 0 row_01_03_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_10

theorem row_01_03_03_11 : b4RowContribution (![1, 4, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 18] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 18 = 30
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 18^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_11

theorem weighted_01_03_03_11 : b4RawGapContribution ![1, 3, 3, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 11] = b4GapPatternWeight 3 3 11 * 0 :=
      b4GapContribution_from_row 1 3 3 11 0 row_01_03_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_11

theorem row_01_03_03_12 : b4RowContribution (![1, 4, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 19] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 19 = 31
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 427 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 19^2 = 427
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_12

theorem weighted_01_03_03_12 : b4RawGapContribution ![1, 3, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 12] = b4GapPatternWeight 3 3 12 * 0 :=
      b4GapContribution_from_row 1 3 3 12 0 row_01_03_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_12

theorem row_01_03_03_13 : b4RowContribution (![1, 4, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 20] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 20 = 32
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 466 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 20^2 = 466
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_13

theorem weighted_01_03_03_13 : b4RawGapContribution ![1, 3, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 13] = b4GapPatternWeight 3 3 13 * 0 :=
      b4GapContribution_from_row 1 3 3 13 0 row_01_03_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_13

theorem row_01_03_03_14 : b4RowContribution (![1, 4, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 21] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 21 = 33
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 507 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 21^2 = 507
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_14

theorem weighted_01_03_03_14 : b4RawGapContribution ![1, 3, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 14] = b4GapPatternWeight 3 3 14 * 0 :=
      b4GapContribution_from_row 1 3 3 14 0 row_01_03_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_14

theorem row_01_03_03_15 : b4RowContribution (![1, 4, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 22] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 22 = 34
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 550 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 22^2 = 550
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_15

theorem weighted_01_03_03_15 : b4RawGapContribution ![1, 3, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 15] = b4GapPatternWeight 3 3 15 * 0 :=
      b4GapContribution_from_row 1 3 3 15 0 row_01_03_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_15

theorem row_01_03_03_16 : b4RowContribution (![1, 4, 7, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 23] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 23 = 35
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 595 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 23^2 = 595
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_16

theorem weighted_01_03_03_16 : b4RawGapContribution ![1, 3, 3, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 16] = b4GapPatternWeight 3 3 16 * 0 :=
      b4GapContribution_from_row 1 3 3 16 0 row_01_03_03_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_16

theorem row_01_03_03_17 : b4RowContribution (![1, 4, 7, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 24] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 24 = 36
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 642 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 24^2 = 642
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_17

theorem weighted_01_03_03_17 : b4RawGapContribution ![1, 3, 3, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 17] = b4GapPatternWeight 3 3 17 * 0 :=
      b4GapContribution_from_row 1 3 3 17 0 row_01_03_03_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_17

theorem row_01_03_03_18 : b4RowContribution (![1, 4, 7, 25] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 7, 25] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 7 + 25 = 37
    decide
  have hzsq : (∑ i, (((![1, 4, 7, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 691 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 7^2 + 25^2 = 691
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_03_18

theorem weighted_01_03_03_18 : b4RawGapContribution ![1, 3, 3, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 3, 18] = b4GapPatternWeight 3 3 18 * 0 :=
      b4GapContribution_from_row 1 3 3 18 0 row_01_03_03_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_03_18

def dvalues_01_03_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 1416, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_03_03

theorem dblock_01_03_03 : b4GapPatternDBlock 1 3 3 = 1416 := by
  calc
    b4GapPatternDBlock 1 3 3 = ∑ d : Fin 19, dvalues_01_03_03 d := by
      apply b4GapDBlock_of_rows 1 3 3 dvalues_01_03_03
      intro d
      fin_cases d
      · exact weighted_01_03_03_00
      · exact weighted_01_03_03_01
      · exact weighted_01_03_03_02
      · exact weighted_01_03_03_03
      · exact weighted_01_03_03_04
      · exact weighted_01_03_03_05
      · exact weighted_01_03_03_06
      · exact weighted_01_03_03_07
      · exact weighted_01_03_03_08
      · exact weighted_01_03_03_09
      · exact weighted_01_03_03_10
      · exact weighted_01_03_03_11
      · exact weighted_01_03_03_12
      · exact weighted_01_03_03_13
      · exact weighted_01_03_03_14
      · exact weighted_01_03_03_15
      · exact weighted_01_03_03_16
      · exact weighted_01_03_03_17
      · exact weighted_01_03_03_18
    _ = 1416 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_03_03

end Paper7MomentGapNumeric
