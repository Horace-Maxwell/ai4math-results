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

theorem row_01_05_00_00 : b4RowContribution (![1, 6, 6, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 6] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 6 = 19
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 109 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 6^2 = 109
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_00

theorem weighted_01_05_00_00 : b4RawGapContribution ![1, 5, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 0] = b4GapPatternWeight 5 0 0 * 0 :=
      b4GapContribution_from_row 1 5 0 0 0 row_01_05_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_00

theorem row_01_05_00_01 : b4RowContribution (![1, 6, 6, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 7] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 7 = 20
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 122 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 7^2 = 122
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_01

theorem weighted_01_05_00_01 : b4RawGapContribution ![1, 5, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 1] = b4GapPatternWeight 5 0 1 * 0 :=
      b4GapContribution_from_row 1 5 0 1 0 row_01_05_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_01

theorem row_01_05_00_02 : b4RowContribution (![1, 6, 6, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 8] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 8 = 21
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 137 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 8^2 = 137
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_02

theorem weighted_01_05_00_02 : b4RawGapContribution ![1, 5, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 2] = b4GapPatternWeight 5 0 2 * 0 :=
      b4GapContribution_from_row 1 5 0 2 0 row_01_05_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_02

theorem row_01_05_00_03 : b4RowContribution (![1, 6, 6, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 9] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 9 = 22
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 154 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 9^2 = 154
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_03

theorem weighted_01_05_00_03 : b4RawGapContribution ![1, 5, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 3] = b4GapPatternWeight 5 0 3 * 0 :=
      b4GapContribution_from_row 1 5 0 3 0 row_01_05_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_03

theorem row_01_05_00_04 : b4RowContribution (![1, 6, 6, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 10] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 10 = 23
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 173 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 10^2 = 173
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_04

theorem weighted_01_05_00_04 : b4RawGapContribution ![1, 5, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 4] = b4GapPatternWeight 5 0 4 * 0 :=
      b4GapContribution_from_row 1 5 0 4 0 row_01_05_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_04

theorem row_01_05_00_05 : b4RowContribution (![1, 6, 6, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 11] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 11 = 24
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 194 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 11^2 = 194
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_05

theorem weighted_01_05_00_05 : b4RawGapContribution ![1, 5, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 5] = b4GapPatternWeight 5 0 5 * 0 :=
      b4GapContribution_from_row 1 5 0 5 0 row_01_05_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_05

def layers_01_05_00_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 13, 11, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 9, 16, 25, 36, 49, 62, 73, 82, 89, 94, 97, 97, 94, 89, 82, 73, 62]]
#print axioms Paper7MomentGapNumeric.layers_01_05_00_06

theorem cells_01_05_00_06 : QTableValid (![1, 6, 6, 12] : Fin 4 → ℕ) layers_01_05_00_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_05_00_06

theorem valid_01_05_00_06 :
    SparseRowValid (![1, 6, 6, 12] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_05_00_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 6, 6, 12] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 1 + 6 + 6 + 12 = 25
      decide
    have hzsq : (∑ i, (((![1, 6, 6, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 217 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 6^2 + 6^2 + 12^2 = 217
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_05_00_06
#print axioms Paper7MomentGapNumeric.valid_01_05_00_06

def qvalues_01_05_00_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 89, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_05_00_06

theorem row_01_05_00_06 : b4RowContribution (![1, 6, 6, 12] : Fin 4 → ℕ) = 89 := by
  calc
    b4RowContribution (![1, 6, 6, 12] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_05_00_06) :=
      sparseRow_sound (![1, 6, 6, 12] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_05_00_06) valid_01_05_00_06
    _ = 89 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_05_00_06 Q := by
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
        _ = 89 := by decide
#print axioms Paper7MomentGapNumeric.row_01_05_00_06

theorem weighted_01_05_00_06 : b4RawGapContribution ![1, 5, 0, 6] = 1068 := by
  calc
    b4RawGapContribution ![1, 5, 0, 6] = b4GapPatternWeight 5 0 6 * 89 :=
      b4GapContribution_from_row 1 5 0 6 89 row_01_05_00_06
    _ = 1068 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_06

theorem row_01_05_00_07 : b4RowContribution (![1, 6, 6, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 13] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 13 = 26
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 242 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 13^2 = 242
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_07

theorem weighted_01_05_00_07 : b4RawGapContribution ![1, 5, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 7] = b4GapPatternWeight 5 0 7 * 0 :=
      b4GapContribution_from_row 1 5 0 7 0 row_01_05_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_07

theorem row_01_05_00_08 : b4RowContribution (![1, 6, 6, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 14] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 14 = 27
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 269 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 14^2 = 269
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_08

theorem weighted_01_05_00_08 : b4RawGapContribution ![1, 5, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 8] = b4GapPatternWeight 5 0 8 * 0 :=
      b4GapContribution_from_row 1 5 0 8 0 row_01_05_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_08

theorem row_01_05_00_09 : b4RowContribution (![1, 6, 6, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 15] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 15 = 28
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 298 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 15^2 = 298
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_09

theorem weighted_01_05_00_09 : b4RawGapContribution ![1, 5, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 9] = b4GapPatternWeight 5 0 9 * 0 :=
      b4GapContribution_from_row 1 5 0 9 0 row_01_05_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_09

theorem row_01_05_00_10 : b4RowContribution (![1, 6, 6, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 16 = 29
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 329 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 16^2 = 329
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_10

theorem weighted_01_05_00_10 : b4RawGapContribution ![1, 5, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 10] = b4GapPatternWeight 5 0 10 * 0 :=
      b4GapContribution_from_row 1 5 0 10 0 row_01_05_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_10

theorem row_01_05_00_11 : b4RowContribution (![1, 6, 6, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 17 = 30
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 362 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 17^2 = 362
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_11

theorem weighted_01_05_00_11 : b4RawGapContribution ![1, 5, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 11] = b4GapPatternWeight 5 0 11 * 0 :=
      b4GapContribution_from_row 1 5 0 11 0 row_01_05_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_11

theorem row_01_05_00_12 : b4RowContribution (![1, 6, 6, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 18 = 31
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 397 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 18^2 = 397
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_12

theorem weighted_01_05_00_12 : b4RawGapContribution ![1, 5, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 12] = b4GapPatternWeight 5 0 12 * 0 :=
      b4GapContribution_from_row 1 5 0 12 0 row_01_05_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_12

theorem row_01_05_00_13 : b4RowContribution (![1, 6, 6, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 19 = 32
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 434 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 19^2 = 434
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_13

theorem weighted_01_05_00_13 : b4RawGapContribution ![1, 5, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 13] = b4GapPatternWeight 5 0 13 * 0 :=
      b4GapContribution_from_row 1 5 0 13 0 row_01_05_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_13

theorem row_01_05_00_14 : b4RowContribution (![1, 6, 6, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 20 = 33
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 473 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 20^2 = 473
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_14

theorem weighted_01_05_00_14 : b4RawGapContribution ![1, 5, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 14] = b4GapPatternWeight 5 0 14 * 0 :=
      b4GapContribution_from_row 1 5 0 14 0 row_01_05_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_14

theorem row_01_05_00_15 : b4RowContribution (![1, 6, 6, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 21] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 21 = 34
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 514 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 21^2 = 514
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_15

theorem weighted_01_05_00_15 : b4RawGapContribution ![1, 5, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 15] = b4GapPatternWeight 5 0 15 * 0 :=
      b4GapContribution_from_row 1 5 0 15 0 row_01_05_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_15

theorem row_01_05_00_16 : b4RowContribution (![1, 6, 6, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 22 = 35
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 557 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 22^2 = 557
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_16

theorem weighted_01_05_00_16 : b4RawGapContribution ![1, 5, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 16] = b4GapPatternWeight 5 0 16 * 0 :=
      b4GapContribution_from_row 1 5 0 16 0 row_01_05_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_16

theorem row_01_05_00_17 : b4RowContribution (![1, 6, 6, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 23 = 36
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 602 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 23^2 = 602
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_17

theorem weighted_01_05_00_17 : b4RawGapContribution ![1, 5, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 17] = b4GapPatternWeight 5 0 17 * 0 :=
      b4GapContribution_from_row 1 5 0 17 0 row_01_05_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_17

theorem row_01_05_00_18 : b4RowContribution (![1, 6, 6, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 6, 6, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 6 + 6 + 24 = 37
    decide
  have hzsq : (∑ i, (((![1, 6, 6, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 649 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 6^2 + 6^2 + 24^2 = 649
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_05_00_18

theorem weighted_01_05_00_18 : b4RawGapContribution ![1, 5, 0, 18] = 0 := by
  calc
    b4RawGapContribution ![1, 5, 0, 18] = b4GapPatternWeight 5 0 18 * 0 :=
      b4GapContribution_from_row 1 5 0 18 0 row_01_05_00_18
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_05_00_18

def dvalues_01_05_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 1068, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_05_00

theorem dblock_01_05_00 : b4GapPatternDBlock 1 5 0 = 1068 := by
  calc
    b4GapPatternDBlock 1 5 0 = ∑ d : Fin 19, dvalues_01_05_00 d := by
      apply b4GapDBlock_of_rows 1 5 0 dvalues_01_05_00
      intro d
      fin_cases d
      · exact weighted_01_05_00_00
      · exact weighted_01_05_00_01
      · exact weighted_01_05_00_02
      · exact weighted_01_05_00_03
      · exact weighted_01_05_00_04
      · exact weighted_01_05_00_05
      · exact weighted_01_05_00_06
      · exact weighted_01_05_00_07
      · exact weighted_01_05_00_08
      · exact weighted_01_05_00_09
      · exact weighted_01_05_00_10
      · exact weighted_01_05_00_11
      · exact weighted_01_05_00_12
      · exact weighted_01_05_00_13
      · exact weighted_01_05_00_14
      · exact weighted_01_05_00_15
      · exact weighted_01_05_00_16
      · exact weighted_01_05_00_17
      · exact weighted_01_05_00_18
    _ = 1068 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_05_00

end Paper7MomentGapNumeric
