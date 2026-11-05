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

theorem row_02_05_00_00 : b4RowContribution (![2, 7, 7, 7] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 7, 7] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 7 + 7 = 23
    decide
  have hzsq : (∑ i, (((![2, 7, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 151 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 7^2 + 7^2 = 151
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_00_00

theorem weighted_02_05_00_00 : b4RawGapContribution ![2, 5, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 0, 0] = b4GapPatternWeight 5 0 0 * 0 :=
      b4GapContribution_from_row 2 5 0 0 0 row_02_05_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_00

theorem row_02_05_00_01 : b4RowContribution (![2, 7, 7, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 7, 8] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 7 + 8 = 24
    decide
  have hzsq : (∑ i, (((![2, 7, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 166 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 7^2 + 8^2 = 166
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_00_01

theorem weighted_02_05_00_01 : b4RawGapContribution ![2, 5, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 0, 1] = b4GapPatternWeight 5 0 1 * 0 :=
      b4GapContribution_from_row 2 5 0 1 0 row_02_05_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_01

theorem row_02_05_00_02 : b4RowContribution (![2, 7, 7, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 7, 9] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 7 + 9 = 25
    decide
  have hzsq : (∑ i, (((![2, 7, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 183 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 7^2 + 9^2 = 183
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_00_02

theorem weighted_02_05_00_02 : b4RawGapContribution ![2, 5, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 0, 2] = b4GapPatternWeight 5 0 2 * 0 :=
      b4GapContribution_from_row 2 5 0 2 0 row_02_05_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_02

theorem row_02_05_00_03 : b4RowContribution (![2, 7, 7, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 7, 10] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 7 + 10 = 26
    decide
  have hzsq : (∑ i, (((![2, 7, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 202 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 7^2 + 10^2 = 202
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_00_03

theorem weighted_02_05_00_03 : b4RawGapContribution ![2, 5, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 0, 3] = b4GapPatternWeight 5 0 3 * 0 :=
      b4GapContribution_from_row 2 5 0 3 0 row_02_05_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_03

def layers_02_05_00_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 22, 21, 18, 15, 12, 9, 6, 3, 1, 0, 0], ![1, 4, 10, 19, 31, 46, 64, 85, 107, 128, 146, 161, 172, 178, 178, 172, 161, 146, 128]]
#print axioms Paper7MomentGapNumeric.layers_02_05_00_04

theorem cells_02_05_00_04 : QTableValid (![2, 7, 7, 11] : Fin 4 → ℕ) layers_02_05_00_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_05_00_04

theorem valid_02_05_00_04 :
    SparseRowValid (![2, 7, 7, 11] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_02_05_00_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 7, 7, 11] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 2 + 7 + 7 + 11 = 27
      decide
    have hzsq : (∑ i, (((![2, 7, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 223 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 7^2 + 7^2 + 11^2 = 223
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_05_00_04
#print axioms Paper7MomentGapNumeric.valid_02_05_00_04

def qvalues_02_05_00_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 146, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_05_00_04

theorem row_02_05_00_04 : b4RowContribution (![2, 7, 7, 11] : Fin 4 → ℕ) = 146 := by
  calc
    b4RowContribution (![2, 7, 7, 11] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_02_05_00_04) :=
      sparseRow_sound (![2, 7, 7, 11] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_02_05_00_04) valid_02_05_00_04
    _ = 146 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_05_00_04 Q := by
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
        _ = 146 := by decide
#print axioms Paper7MomentGapNumeric.row_02_05_00_04

theorem weighted_02_05_00_04 : b4RawGapContribution ![2, 5, 0, 4] = 1752 := by
  calc
    b4RawGapContribution ![2, 5, 0, 4] = b4GapPatternWeight 5 0 4 * 146 :=
      b4GapContribution_from_row 2 5 0 4 146 row_02_05_00_04
    _ = 1752 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_04

theorem row_02_05_00_05 : b4RowContribution (![2, 7, 7, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 7, 12] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 7 + 12 = 28
    decide
  have hzsq : (∑ i, (((![2, 7, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 246 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 7^2 + 12^2 = 246
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_00_05

theorem weighted_02_05_00_05 : b4RawGapContribution ![2, 5, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 0, 5] = b4GapPatternWeight 5 0 5 * 0 :=
      b4GapContribution_from_row 2 5 0 5 0 row_02_05_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_05

def layers_02_05_00_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 22, 21, 18, 15, 12, 9, 6, 3, 1, 0, 0], ![1, 4, 10, 19, 31, 46, 64, 85, 107, 128, 146, 161, 173, 182, 187, 187, 182, 173, 161]]
#print axioms Paper7MomentGapNumeric.layers_02_05_00_06

theorem cells_02_05_00_06 : QTableValid (![2, 7, 7, 13] : Fin 4 → ℕ) layers_02_05_00_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_05_00_06

theorem valid_02_05_00_06 :
    SparseRowValid (![2, 7, 7, 13] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_02_05_00_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 7, 7, 13] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 2 + 7 + 7 + 13 = 29
      decide
    have hzsq : (∑ i, (((![2, 7, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 271 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 7^2 + 7^2 + 13^2 = 271
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_05_00_06
#print axioms Paper7MomentGapNumeric.valid_02_05_00_06

def qvalues_02_05_00_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 85, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_05_00_06

theorem row_02_05_00_06 : b4RowContribution (![2, 7, 7, 13] : Fin 4 → ℕ) = 85 := by
  calc
    b4RowContribution (![2, 7, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_02_05_00_06) :=
      sparseRow_sound (![2, 7, 7, 13] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_02_05_00_06) valid_02_05_00_06
    _ = 85 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_05_00_06 Q := by
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
        _ = 85 := by decide
#print axioms Paper7MomentGapNumeric.row_02_05_00_06

theorem weighted_02_05_00_06 : b4RawGapContribution ![2, 5, 0, 6] = 1020 := by
  calc
    b4RawGapContribution ![2, 5, 0, 6] = b4GapPatternWeight 5 0 6 * 85 :=
      b4GapContribution_from_row 2 5 0 6 85 row_02_05_00_06
    _ = 1020 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_06

theorem row_02_05_00_07 : b4RowContribution (![2, 7, 7, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 7, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 7 + 14 = 30
    decide
  have hzsq : (∑ i, (((![2, 7, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 298 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 7^2 + 14^2 = 298
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_00_07

theorem weighted_02_05_00_07 : b4RawGapContribution ![2, 5, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 0, 7] = b4GapPatternWeight 5 0 7 * 0 :=
      b4GapContribution_from_row 2 5 0 7 0 row_02_05_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_07

theorem row_02_05_00_08 : b4RowContribution (![2, 7, 7, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 7, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 7 + 15 = 31
    decide
  have hzsq : (∑ i, (((![2, 7, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 327 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 7^2 + 15^2 = 327
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_00_08

theorem weighted_02_05_00_08 : b4RawGapContribution ![2, 5, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 0, 8] = b4GapPatternWeight 5 0 8 * 0 :=
      b4GapContribution_from_row 2 5 0 8 0 row_02_05_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_08

theorem row_02_05_00_09 : b4RowContribution (![2, 7, 7, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 7, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 7 + 16 = 32
    decide
  have hzsq : (∑ i, (((![2, 7, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 358 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 7^2 + 16^2 = 358
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_00_09

theorem weighted_02_05_00_09 : b4RawGapContribution ![2, 5, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 0, 9] = b4GapPatternWeight 5 0 9 * 0 :=
      b4GapContribution_from_row 2 5 0 9 0 row_02_05_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_09

theorem row_02_05_00_10 : b4RowContribution (![2, 7, 7, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 7, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 7 + 17 = 33
    decide
  have hzsq : (∑ i, (((![2, 7, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 391 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 7^2 + 17^2 = 391
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_00_10

theorem weighted_02_05_00_10 : b4RawGapContribution ![2, 5, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 0, 10] = b4GapPatternWeight 5 0 10 * 0 :=
      b4GapContribution_from_row 2 5 0 10 0 row_02_05_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_10

theorem row_02_05_00_11 : b4RowContribution (![2, 7, 7, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 7, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 7 + 18 = 34
    decide
  have hzsq : (∑ i, (((![2, 7, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 426 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 7^2 + 18^2 = 426
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_00_11

theorem weighted_02_05_00_11 : b4RawGapContribution ![2, 5, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 0, 11] = b4GapPatternWeight 5 0 11 * 0 :=
      b4GapContribution_from_row 2 5 0 11 0 row_02_05_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_11

theorem row_02_05_00_12 : b4RowContribution (![2, 7, 7, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 7, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 7 + 19 = 35
    decide
  have hzsq : (∑ i, (((![2, 7, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 463 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 7^2 + 19^2 = 463
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_00_12

theorem weighted_02_05_00_12 : b4RawGapContribution ![2, 5, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 0, 12] = b4GapPatternWeight 5 0 12 * 0 :=
      b4GapContribution_from_row 2 5 0 12 0 row_02_05_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_12

theorem row_02_05_00_13 : b4RowContribution (![2, 7, 7, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 7, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 7 + 20 = 36
    decide
  have hzsq : (∑ i, (((![2, 7, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 502 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 7^2 + 20^2 = 502
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_00_13

theorem weighted_02_05_00_13 : b4RawGapContribution ![2, 5, 0, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 0, 13] = b4GapPatternWeight 5 0 13 * 0 :=
      b4GapContribution_from_row 2 5 0 13 0 row_02_05_00_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_13

theorem row_02_05_00_14 : b4RowContribution (![2, 7, 7, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 7, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 7 + 21 = 37
    decide
  have hzsq : (∑ i, (((![2, 7, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 543 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 7^2 + 21^2 = 543
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_00_14

theorem weighted_02_05_00_14 : b4RawGapContribution ![2, 5, 0, 14] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 0, 14] = b4GapPatternWeight 5 0 14 * 0 :=
      b4GapContribution_from_row 2 5 0 14 0 row_02_05_00_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_00_14

def dvalues_02_05_00 : Fin 15 → ℕ := ![0, 0, 0, 0, 1752, 0, 1020, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_05_00

theorem dblock_02_05_00 : b4GapPatternDBlock 2 5 0 = 2772 := by
  calc
    b4GapPatternDBlock 2 5 0 = ∑ d : Fin 15, dvalues_02_05_00 d := by
      apply b4GapDBlock_of_rows 2 5 0 dvalues_02_05_00
      intro d
      fin_cases d
      · exact weighted_02_05_00_00
      · exact weighted_02_05_00_01
      · exact weighted_02_05_00_02
      · exact weighted_02_05_00_03
      · exact weighted_02_05_00_04
      · exact weighted_02_05_00_05
      · exact weighted_02_05_00_06
      · exact weighted_02_05_00_07
      · exact weighted_02_05_00_08
      · exact weighted_02_05_00_09
      · exact weighted_02_05_00_10
      · exact weighted_02_05_00_11
      · exact weighted_02_05_00_12
      · exact weighted_02_05_00_13
      · exact weighted_02_05_00_14
    _ = 2772 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_05_00

end Paper7MomentGapNumeric
