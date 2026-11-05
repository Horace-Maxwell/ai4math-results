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

theorem row_05_00_00_00 : b4RowContribution (![5, 5, 5, 5] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 5] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 5 = 20
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 100 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 5^2 = 100
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_00

theorem weighted_05_00_00_00 : b4RawGapContribution ![5, 0, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 0] = b4GapPatternWeight 0 0 0 * 0 :=
      b4GapContribution_from_row 5 0 0 0 0 row_05_00_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_00

theorem row_05_00_00_01 : b4RowContribution (![5, 5, 5, 6] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 6] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 6 = 21
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 111 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 6^2 = 111
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_01

theorem weighted_05_00_00_01 : b4RawGapContribution ![5, 0, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 1] = b4GapPatternWeight 0 0 1 * 0 :=
      b4GapContribution_from_row 5 0 0 1 0 row_05_00_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_01

theorem row_05_00_00_02 : b4RowContribution (![5, 5, 5, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 7] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 7 = 22
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 124 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 7^2 = 124
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_02

theorem weighted_05_00_00_02 : b4RawGapContribution ![5, 0, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 2] = b4GapPatternWeight 0 0 2 * 0 :=
      b4GapContribution_from_row 5 0 0 2 0 row_05_00_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_02

theorem row_05_00_00_03 : b4RowContribution (![5, 5, 5, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 8] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 8 = 23
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 139 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 8^2 = 139
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_03

theorem weighted_05_00_00_03 : b4RawGapContribution ![5, 0, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 3] = b4GapPatternWeight 0 0 3 * 0 :=
      b4GapContribution_from_row 5 0 0 3 0 row_05_00_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_03

theorem row_05_00_00_04 : b4RowContribution (![5, 5, 5, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 9] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 9 = 24
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 156 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 9^2 = 156
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_04

theorem weighted_05_00_00_04 : b4RawGapContribution ![5, 0, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 4] = b4GapPatternWeight 0 0 4 * 0 :=
      b4GapContribution_from_row 5 0 0 4 0 row_05_00_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_04

theorem row_05_00_00_05 : b4RowContribution (![5, 5, 5, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 10] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 10 = 25
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 175 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 10^2 = 175
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_05

theorem weighted_05_00_00_05 : b4RawGapContribution ![5, 0, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 5] = b4GapPatternWeight 0 0 5 * 0 :=
      b4GapContribution_from_row 5 0 0 5 0 row_05_00_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_05

theorem row_05_00_00_06 : b4RowContribution (![5, 5, 5, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 11] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 11 = 26
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 196 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 11^2 = 196
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_06

theorem weighted_05_00_00_06 : b4RawGapContribution ![5, 0, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 6] = b4GapPatternWeight 0 0 6 * 0 :=
      b4GapContribution_from_row 5 0 0 6 0 row_05_00_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_06

theorem row_05_00_00_07 : b4RowContribution (![5, 5, 5, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 12] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 12 = 27
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 219 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 12^2 = 219
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_07

theorem weighted_05_00_00_07 : b4RawGapContribution ![5, 0, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 7] = b4GapPatternWeight 0 0 7 * 0 :=
      b4GapContribution_from_row 5 0 0 7 0 row_05_00_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_07

theorem row_05_00_00_08 : b4RowContribution (![5, 5, 5, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 13 = 28
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 244 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 13^2 = 244
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_08

theorem weighted_05_00_00_08 : b4RawGapContribution ![5, 0, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 8] = b4GapPatternWeight 0 0 8 * 0 :=
      b4GapContribution_from_row 5 0 0 8 0 row_05_00_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_08

def layers_05_00_00_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 25, 27, 27, 25, 21, 15, 10, 6, 3, 1, 0, 0, 0], ![1, 4, 10, 20, 35, 56, 81, 108, 135, 160, 181, 196, 206, 212, 215, 215, 212, 206, 196]]
#print axioms Paper7MomentGapNumeric.layers_05_00_00_09

theorem cells_05_00_00_09 : QTableValid (![5, 5, 5, 14] : Fin 4 → ℕ) layers_05_00_00_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_05_00_00_09

theorem valid_05_00_00_09 :
    SparseRowValid (![5, 5, 5, 14] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_05_00_00_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![5, 5, 5, 14] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 5 + 5 + 5 + 14 = 29
      decide
    have hzsq : (∑ i, (((![5, 5, 5, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 271 := by
      rw [Fin.sum_univ_four]
      change (5 : ℤ)^2 + 5^2 + 5^2 + 14^2 = 271
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_05_00_00_09
#print axioms Paper7MomentGapNumeric.valid_05_00_00_09

def qvalues_05_00_00_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 108, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_05_00_00_09

theorem row_05_00_00_09 : b4RowContribution (![5, 5, 5, 14] : Fin 4 → ℕ) = 108 := by
  calc
    b4RowContribution (![5, 5, 5, 14] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_05_00_00_09) :=
      sparseRow_sound (![5, 5, 5, 14] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_05_00_00_09) valid_05_00_00_09
    _ = 108 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_05_00_00_09 Q := by
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
        _ = 108 := by decide
#print axioms Paper7MomentGapNumeric.row_05_00_00_09

theorem weighted_05_00_00_09 : b4RawGapContribution ![5, 0, 0, 9] = 432 := by
  calc
    b4RawGapContribution ![5, 0, 0, 9] = b4GapPatternWeight 0 0 9 * 108 :=
      b4GapContribution_from_row 5 0 0 9 108 row_05_00_00_09
    _ = 432 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_09

theorem row_05_00_00_10 : b4RowContribution (![5, 5, 5, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 15 = 30
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 300 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 15^2 = 300
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_10

theorem weighted_05_00_00_10 : b4RawGapContribution ![5, 0, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 10] = b4GapPatternWeight 0 0 10 * 0 :=
      b4GapContribution_from_row 5 0 0 10 0 row_05_00_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_10

theorem row_05_00_00_11 : b4RowContribution (![5, 5, 5, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 16 = 31
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 331 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 16^2 = 331
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_11

theorem weighted_05_00_00_11 : b4RawGapContribution ![5, 0, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 11] = b4GapPatternWeight 0 0 11 * 0 :=
      b4GapContribution_from_row 5 0 0 11 0 row_05_00_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_11

theorem row_05_00_00_12 : b4RowContribution (![5, 5, 5, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 17 = 32
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 364 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 17^2 = 364
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_12

theorem weighted_05_00_00_12 : b4RawGapContribution ![5, 0, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 12] = b4GapPatternWeight 0 0 12 * 0 :=
      b4GapContribution_from_row 5 0 0 12 0 row_05_00_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_12

theorem row_05_00_00_13 : b4RowContribution (![5, 5, 5, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 18 = 33
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 399 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 18^2 = 399
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_13

theorem weighted_05_00_00_13 : b4RawGapContribution ![5, 0, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 13] = b4GapPatternWeight 0 0 13 * 0 :=
      b4GapContribution_from_row 5 0 0 13 0 row_05_00_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_13

theorem row_05_00_00_14 : b4RowContribution (![5, 5, 5, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 19 = 34
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 436 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 19^2 = 436
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_14

theorem weighted_05_00_00_14 : b4RawGapContribution ![5, 0, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 14] = b4GapPatternWeight 0 0 14 * 0 :=
      b4GapContribution_from_row 5 0 0 14 0 row_05_00_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_14

theorem row_05_00_00_15 : b4RowContribution (![5, 5, 5, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 20 = 35
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 475 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 20^2 = 475
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_15

theorem weighted_05_00_00_15 : b4RawGapContribution ![5, 0, 0, 15] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 15] = b4GapPatternWeight 0 0 15 * 0 :=
      b4GapContribution_from_row 5 0 0 15 0 row_05_00_00_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_15

theorem row_05_00_00_16 : b4RowContribution (![5, 5, 5, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 21 = 36
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 516 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 21^2 = 516
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_16

theorem weighted_05_00_00_16 : b4RawGapContribution ![5, 0, 0, 16] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 16] = b4GapPatternWeight 0 0 16 * 0 :=
      b4GapContribution_from_row 5 0 0 16 0 row_05_00_00_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_16

theorem row_05_00_00_17 : b4RowContribution (![5, 5, 5, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 5, 5, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 5 + 5 + 22 = 37
    decide
  have hzsq : (∑ i, (((![5, 5, 5, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 559 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 5^2 + 5^2 + 22^2 = 559
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_00_00_17

theorem weighted_05_00_00_17 : b4RawGapContribution ![5, 0, 0, 17] = 0 := by
  calc
    b4RawGapContribution ![5, 0, 0, 17] = b4GapPatternWeight 0 0 17 * 0 :=
      b4GapContribution_from_row 5 0 0 17 0 row_05_00_00_17
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_00_00_17

def dvalues_05_00_00 : Fin 18 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 432, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_00_00

theorem dblock_05_00_00 : b4GapPatternDBlock 5 0 0 = 432 := by
  calc
    b4GapPatternDBlock 5 0 0 = ∑ d : Fin 18, dvalues_05_00_00 d := by
      apply b4GapDBlock_of_rows 5 0 0 dvalues_05_00_00
      intro d
      fin_cases d
      · exact weighted_05_00_00_00
      · exact weighted_05_00_00_01
      · exact weighted_05_00_00_02
      · exact weighted_05_00_00_03
      · exact weighted_05_00_00_04
      · exact weighted_05_00_00_05
      · exact weighted_05_00_00_06
      · exact weighted_05_00_00_07
      · exact weighted_05_00_00_08
      · exact weighted_05_00_00_09
      · exact weighted_05_00_00_10
      · exact weighted_05_00_00_11
      · exact weighted_05_00_00_12
      · exact weighted_05_00_00_13
      · exact weighted_05_00_00_14
      · exact weighted_05_00_00_15
      · exact weighted_05_00_00_16
      · exact weighted_05_00_00_17
    _ = 432 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_00_00

end Paper7MomentGapNumeric
