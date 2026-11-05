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

theorem row_02_04_01_00 : b4RowContribution (![2, 6, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 7, 7] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 7 + 7 = 22
    decide
  have hzsq : (∑ i, (((![2, 6, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 138 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 7^2 + 7^2 = 138
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_01_00

theorem weighted_02_04_01_00 : b4RawGapContribution ![2, 4, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 1, 0] = b4GapPatternWeight 4 1 0 * 0 :=
      b4GapContribution_from_row 2 4 1 0 0 row_02_04_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_00

theorem row_02_04_01_01 : b4RowContribution (![2, 6, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 7, 8] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 7 + 8 = 23
    decide
  have hzsq : (∑ i, (((![2, 6, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 153 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 7^2 + 8^2 = 153
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_01_01

theorem weighted_02_04_01_01 : b4RawGapContribution ![2, 4, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 1, 1] = b4GapPatternWeight 4 1 1 * 0 :=
      b4GapContribution_from_row 2 4 1 1 0 row_02_04_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_01

theorem row_02_04_01_02 : b4RowContribution (![2, 6, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 7, 9] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 7 + 9 = 24
    decide
  have hzsq : (∑ i, (((![2, 6, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 170 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 7^2 + 9^2 = 170
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_01_02

theorem weighted_02_04_01_02 : b4RawGapContribution ![2, 4, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 1, 2] = b4GapPatternWeight 4 1 2 * 0 :=
      b4GapContribution_from_row 2 4 1 2 0 row_02_04_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_02

theorem row_02_04_01_03 : b4RowContribution (![2, 6, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 7, 10] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 7 + 10 = 25
    decide
  have hzsq : (∑ i, (((![2, 6, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 189 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 7^2 + 10^2 = 189
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_01_03

theorem weighted_02_04_01_03 : b4RawGapContribution ![2, 4, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 1, 3] = b4GapPatternWeight 4 1 3 * 0 :=
      b4GapContribution_from_row 2 4 1 3 0 row_02_04_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_03

theorem row_02_04_01_04 : b4RowContribution (![2, 6, 7, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 7, 11] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 7 + 11 = 26
    decide
  have hzsq : (∑ i, (((![2, 6, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 210 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 7^2 + 11^2 = 210
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_01_04

theorem weighted_02_04_01_04 : b4RawGapContribution ![2, 4, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 1, 4] = b4GapPatternWeight 4 1 4 * 0 :=
      b4GapContribution_from_row 2 4 1 4 0 row_02_04_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_04

def layers_02_04_01_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 20, 20, 18, 15, 12, 9, 6, 3, 1, 0, 0, 0], ![1, 4, 10, 19, 31, 46, 64, 84, 104, 122, 137, 149, 158, 163, 163, 158, 149, 137, 122]]
#print axioms Paper7MomentGapNumeric.layers_02_04_01_05

theorem cells_02_04_01_05 : QTableValid (![2, 6, 7, 12] : Fin 4 → ℕ) layers_02_04_01_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_04_01_05

theorem valid_02_04_01_05 :
    SparseRowValid (![2, 6, 7, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_02_04_01_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 6, 7, 12] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 2 + 6 + 7 + 12 = 27
      decide
    have hzsq : (∑ i, (((![2, 6, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 233 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 6^2 + 7^2 + 12^2 = 233
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_04_01_05
#print axioms Paper7MomentGapNumeric.valid_02_04_01_05

def qvalues_02_04_01_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_04_01_05

theorem row_02_04_01_05 : b4RowContribution (![2, 6, 7, 12] : Fin 4 → ℕ) = 46 := by
  calc
    b4RowContribution (![2, 6, 7, 12] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_02_04_01_05) :=
      sparseRow_sound (![2, 6, 7, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_02_04_01_05) valid_02_04_01_05
    _ = 46 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_04_01_05 Q := by
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
        _ = 46 := by decide
#print axioms Paper7MomentGapNumeric.row_02_04_01_05

theorem weighted_02_04_01_05 : b4RawGapContribution ![2, 4, 1, 5] = 1104 := by
  calc
    b4RawGapContribution ![2, 4, 1, 5] = b4GapPatternWeight 4 1 5 * 46 :=
      b4GapContribution_from_row 2 4 1 5 46 row_02_04_01_05
    _ = 1104 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_05

theorem row_02_04_01_06 : b4RowContribution (![2, 6, 7, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 7, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 7 + 13 = 28
    decide
  have hzsq : (∑ i, (((![2, 6, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 258 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 7^2 + 13^2 = 258
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_01_06

theorem weighted_02_04_01_06 : b4RawGapContribution ![2, 4, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 1, 6] = b4GapPatternWeight 4 1 6 * 0 :=
      b4GapContribution_from_row 2 4 1 6 0 row_02_04_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_06

def layers_02_04_01_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 20, 20, 18, 15, 12, 9, 6, 3, 1, 0, 0, 0], ![1, 4, 10, 19, 31, 46, 64, 84, 104, 122, 137, 149, 158, 164, 167, 167, 164, 158, 149]]
#print axioms Paper7MomentGapNumeric.layers_02_04_01_07

theorem cells_02_04_01_07 : QTableValid (![2, 6, 7, 14] : Fin 4 → ℕ) layers_02_04_01_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_04_01_07

theorem valid_02_04_01_07 :
    SparseRowValid (![2, 6, 7, 14] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_02_04_01_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 6, 7, 14] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 2 + 6 + 7 + 14 = 29
      decide
    have hzsq : (∑ i, (((![2, 6, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 285 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 6^2 + 7^2 + 14^2 = 285
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_04_01_07
#print axioms Paper7MomentGapNumeric.valid_02_04_01_07

def qvalues_02_04_01_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_04_01_07

theorem row_02_04_01_07 : b4RowContribution (![2, 6, 7, 14] : Fin 4 → ℕ) = 64 := by
  calc
    b4RowContribution (![2, 6, 7, 14] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_02_04_01_07) :=
      sparseRow_sound (![2, 6, 7, 14] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_02_04_01_07) valid_02_04_01_07
    _ = 64 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_04_01_07 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 64 := by decide
#print axioms Paper7MomentGapNumeric.row_02_04_01_07

theorem weighted_02_04_01_07 : b4RawGapContribution ![2, 4, 1, 7] = 1536 := by
  calc
    b4RawGapContribution ![2, 4, 1, 7] = b4GapPatternWeight 4 1 7 * 64 :=
      b4GapContribution_from_row 2 4 1 7 64 row_02_04_01_07
    _ = 1536 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_07

theorem row_02_04_01_08 : b4RowContribution (![2, 6, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 7, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 7 + 15 = 30
    decide
  have hzsq : (∑ i, (((![2, 6, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 314 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 7^2 + 15^2 = 314
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_01_08

theorem weighted_02_04_01_08 : b4RawGapContribution ![2, 4, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 1, 8] = b4GapPatternWeight 4 1 8 * 0 :=
      b4GapContribution_from_row 2 4 1 8 0 row_02_04_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_08

theorem row_02_04_01_09 : b4RowContribution (![2, 6, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 7, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 7 + 16 = 31
    decide
  have hzsq : (∑ i, (((![2, 6, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 345 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 7^2 + 16^2 = 345
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_01_09

theorem weighted_02_04_01_09 : b4RawGapContribution ![2, 4, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 1, 9] = b4GapPatternWeight 4 1 9 * 0 :=
      b4GapContribution_from_row 2 4 1 9 0 row_02_04_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_09

theorem row_02_04_01_10 : b4RowContribution (![2, 6, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 7, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 7 + 17 = 32
    decide
  have hzsq : (∑ i, (((![2, 6, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 378 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 7^2 + 17^2 = 378
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_01_10

theorem weighted_02_04_01_10 : b4RawGapContribution ![2, 4, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 1, 10] = b4GapPatternWeight 4 1 10 * 0 :=
      b4GapContribution_from_row 2 4 1 10 0 row_02_04_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_10

theorem row_02_04_01_11 : b4RowContribution (![2, 6, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 7, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 7 + 18 = 33
    decide
  have hzsq : (∑ i, (((![2, 6, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 413 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 7^2 + 18^2 = 413
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_01_11

theorem weighted_02_04_01_11 : b4RawGapContribution ![2, 4, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 1, 11] = b4GapPatternWeight 4 1 11 * 0 :=
      b4GapContribution_from_row 2 4 1 11 0 row_02_04_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_11

theorem row_02_04_01_12 : b4RowContribution (![2, 6, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 7, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 7 + 19 = 34
    decide
  have hzsq : (∑ i, (((![2, 6, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 7^2 + 19^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_01_12

theorem weighted_02_04_01_12 : b4RawGapContribution ![2, 4, 1, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 1, 12] = b4GapPatternWeight 4 1 12 * 0 :=
      b4GapContribution_from_row 2 4 1 12 0 row_02_04_01_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_12

theorem row_02_04_01_13 : b4RowContribution (![2, 6, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 7, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 7 + 20 = 35
    decide
  have hzsq : (∑ i, (((![2, 6, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 489 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 7^2 + 20^2 = 489
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_01_13

theorem weighted_02_04_01_13 : b4RawGapContribution ![2, 4, 1, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 1, 13] = b4GapPatternWeight 4 1 13 * 0 :=
      b4GapContribution_from_row 2 4 1 13 0 row_02_04_01_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_13

theorem row_02_04_01_14 : b4RowContribution (![2, 6, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 7, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 7 + 21 = 36
    decide
  have hzsq : (∑ i, (((![2, 6, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 530 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 7^2 + 21^2 = 530
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_01_14

theorem weighted_02_04_01_14 : b4RawGapContribution ![2, 4, 1, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 1, 14] = b4GapPatternWeight 4 1 14 * 0 :=
      b4GapContribution_from_row 2 4 1 14 0 row_02_04_01_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_14

theorem row_02_04_01_15 : b4RowContribution (![2, 6, 7, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 7, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 7 + 22 = 37
    decide
  have hzsq : (∑ i, (((![2, 6, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 573 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 7^2 + 22^2 = 573
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_01_15

theorem weighted_02_04_01_15 : b4RawGapContribution ![2, 4, 1, 15] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 1, 15] = b4GapPatternWeight 4 1 15 * 0 :=
      b4GapContribution_from_row 2 4 1 15 0 row_02_04_01_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_01_15

def dvalues_02_04_01 : Fin 16 → ℕ := ![0, 0, 0, 0, 0, 1104, 0, 1536, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_04_01

theorem dblock_02_04_01 : b4GapPatternDBlock 2 4 1 = 2640 := by
  calc
    b4GapPatternDBlock 2 4 1 = ∑ d : Fin 16, dvalues_02_04_01 d := by
      apply b4GapDBlock_of_rows 2 4 1 dvalues_02_04_01
      intro d
      fin_cases d
      · exact weighted_02_04_01_00
      · exact weighted_02_04_01_01
      · exact weighted_02_04_01_02
      · exact weighted_02_04_01_03
      · exact weighted_02_04_01_04
      · exact weighted_02_04_01_05
      · exact weighted_02_04_01_06
      · exact weighted_02_04_01_07
      · exact weighted_02_04_01_08
      · exact weighted_02_04_01_09
      · exact weighted_02_04_01_10
      · exact weighted_02_04_01_11
      · exact weighted_02_04_01_12
      · exact weighted_02_04_01_13
      · exact weighted_02_04_01_14
      · exact weighted_02_04_01_15
    _ = 2640 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_04_01

end Paper7MomentGapNumeric
