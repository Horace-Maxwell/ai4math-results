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

theorem row_01_07_00_00 : b4RowContribution (![1, 8, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 8, 8] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 8 + 8 = 25
    decide
  have hzsq : (∑ i, (((![1, 8, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 193 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 8^2 + 8^2 = 193
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_00_00

theorem weighted_01_07_00_00 : b4RawGapContribution ![1, 7, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 0, 0] = b4GapPatternWeight 7 0 0 * 0 :=
      b4GapContribution_from_row 1 7 0 0 0 row_01_07_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_00_00

theorem row_01_07_00_01 : b4RowContribution (![1, 8, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 8, 9] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 8 + 9 = 26
    decide
  have hzsq : (∑ i, (((![1, 8, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 210 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 8^2 + 9^2 = 210
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_00_01

theorem weighted_01_07_00_01 : b4RawGapContribution ![1, 7, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 0, 1] = b4GapPatternWeight 7 0 1 * 0 :=
      b4GapContribution_from_row 1 7 0 1 0 row_01_07_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_00_01

def layers_01_07_00_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 17, 15, 13, 11, 9, 7, 5, 3, 1, 0], ![1, 4, 9, 16, 25, 36, 49, 64, 81, 98, 113, 125, 133, 137, 137, 133, 125, 113, 98]]
#print axioms Paper7MomentGapNumeric.layers_01_07_00_02

theorem cells_01_07_00_02 : QTableValid (![1, 8, 8, 10] : Fin 4 → ℕ) layers_01_07_00_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_07_00_02

theorem valid_01_07_00_02 :
    SparseRowValid (![1, 8, 8, 10] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_07_00_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 8, 8, 10] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 1 + 8 + 8 + 10 = 27
      decide
    have hzsq : (∑ i, (((![1, 8, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 229 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 8^2 + 8^2 + 10^2 = 229
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_07_00_02
#print axioms Paper7MomentGapNumeric.valid_01_07_00_02

def qvalues_01_07_00_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_07_00_02

theorem row_01_07_00_02 : b4RowContribution (![1, 8, 8, 10] : Fin 4 → ℕ) = 64 := by
  calc
    b4RowContribution (![1, 8, 8, 10] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_01_07_00_02) :=
      sparseRow_sound (![1, 8, 8, 10] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_07_00_02) valid_01_07_00_02
    _ = 64 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_07_00_02 Q := by
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
        _ = 64 := by decide
#print axioms Paper7MomentGapNumeric.row_01_07_00_02

theorem weighted_01_07_00_02 : b4RawGapContribution ![1, 7, 0, 2] = 768 := by
  calc
    b4RawGapContribution ![1, 7, 0, 2] = b4GapPatternWeight 7 0 2 * 64 :=
      b4GapContribution_from_row 1 7 0 2 64 row_01_07_00_02
    _ = 768 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_00_02

theorem row_01_07_00_03 : b4RowContribution (![1, 8, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 8, 11] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 8 + 11 = 28
    decide
  have hzsq : (∑ i, (((![1, 8, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 250 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 8^2 + 11^2 = 250
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_00_03

theorem weighted_01_07_00_03 : b4RawGapContribution ![1, 7, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 0, 3] = b4GapPatternWeight 7 0 3 * 0 :=
      b4GapContribution_from_row 1 7 0 3 0 row_01_07_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_00_03

def layers_01_07_00_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 17, 15, 13, 11, 9, 7, 5, 3, 1, 0], ![1, 4, 9, 16, 25, 36, 49, 64, 81, 98, 113, 126, 137, 145, 149, 149, 145, 137, 126]]
#print axioms Paper7MomentGapNumeric.layers_01_07_00_04

theorem cells_01_07_00_04 : QTableValid (![1, 8, 8, 12] : Fin 4 → ℕ) layers_01_07_00_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_07_00_04

theorem valid_01_07_00_04 :
    SparseRowValid (![1, 8, 8, 12] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_01_07_00_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 8, 8, 12] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 1 + 8 + 8 + 12 = 29
      decide
    have hzsq : (∑ i, (((![1, 8, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 273 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 8^2 + 8^2 + 12^2 = 273
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_07_00_04
#print axioms Paper7MomentGapNumeric.valid_01_07_00_04

def qvalues_01_07_00_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_07_00_04

theorem row_01_07_00_04 : b4RowContribution (![1, 8, 8, 12] : Fin 4 → ℕ) = 49 := by
  calc
    b4RowContribution (![1, 8, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_01_07_00_04) :=
      sparseRow_sound (![1, 8, 8, 12] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_01_07_00_04) valid_01_07_00_04
    _ = 49 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_07_00_04 Q := by
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
        _ = 49 := by decide
#print axioms Paper7MomentGapNumeric.row_01_07_00_04

theorem weighted_01_07_00_04 : b4RawGapContribution ![1, 7, 0, 4] = 588 := by
  calc
    b4RawGapContribution ![1, 7, 0, 4] = b4GapPatternWeight 7 0 4 * 49 :=
      b4GapContribution_from_row 1 7 0 4 49 row_01_07_00_04
    _ = 588 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_00_04

theorem row_01_07_00_05 : b4RowContribution (![1, 8, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 8, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 8 + 13 = 30
    decide
  have hzsq : (∑ i, (((![1, 8, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 298 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 8^2 + 13^2 = 298
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_00_05

theorem weighted_01_07_00_05 : b4RawGapContribution ![1, 7, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 0, 5] = b4GapPatternWeight 7 0 5 * 0 :=
      b4GapContribution_from_row 1 7 0 5 0 row_01_07_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_00_05

theorem row_01_07_00_06 : b4RowContribution (![1, 8, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 8, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 8 + 14 = 31
    decide
  have hzsq : (∑ i, (((![1, 8, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 8^2 + 14^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_00_06

theorem weighted_01_07_00_06 : b4RawGapContribution ![1, 7, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 0, 6] = b4GapPatternWeight 7 0 6 * 0 :=
      b4GapContribution_from_row 1 7 0 6 0 row_01_07_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_00_06

theorem row_01_07_00_07 : b4RowContribution (![1, 8, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 8, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 8 + 15 = 32
    decide
  have hzsq : (∑ i, (((![1, 8, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 354 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 8^2 + 15^2 = 354
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_00_07

theorem weighted_01_07_00_07 : b4RawGapContribution ![1, 7, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 0, 7] = b4GapPatternWeight 7 0 7 * 0 :=
      b4GapContribution_from_row 1 7 0 7 0 row_01_07_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_00_07

theorem row_01_07_00_08 : b4RowContribution (![1, 8, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 8, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 8 + 16 = 33
    decide
  have hzsq : (∑ i, (((![1, 8, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 385 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 8^2 + 16^2 = 385
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_00_08

theorem weighted_01_07_00_08 : b4RawGapContribution ![1, 7, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 0, 8] = b4GapPatternWeight 7 0 8 * 0 :=
      b4GapContribution_from_row 1 7 0 8 0 row_01_07_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_00_08

theorem row_01_07_00_09 : b4RowContribution (![1, 8, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 8, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 8 + 17 = 34
    decide
  have hzsq : (∑ i, (((![1, 8, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 418 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 8^2 + 17^2 = 418
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_00_09

theorem weighted_01_07_00_09 : b4RawGapContribution ![1, 7, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 0, 9] = b4GapPatternWeight 7 0 9 * 0 :=
      b4GapContribution_from_row 1 7 0 9 0 row_01_07_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_00_09

theorem row_01_07_00_10 : b4RowContribution (![1, 8, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 8, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 8 + 18 = 35
    decide
  have hzsq : (∑ i, (((![1, 8, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 453 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 8^2 + 18^2 = 453
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_00_10

theorem weighted_01_07_00_10 : b4RawGapContribution ![1, 7, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 0, 10] = b4GapPatternWeight 7 0 10 * 0 :=
      b4GapContribution_from_row 1 7 0 10 0 row_01_07_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_00_10

theorem row_01_07_00_11 : b4RowContribution (![1, 8, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 8, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 8 + 19 = 36
    decide
  have hzsq : (∑ i, (((![1, 8, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 490 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 8^2 + 19^2 = 490
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_00_11

theorem weighted_01_07_00_11 : b4RawGapContribution ![1, 7, 0, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 0, 11] = b4GapPatternWeight 7 0 11 * 0 :=
      b4GapContribution_from_row 1 7 0 11 0 row_01_07_00_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_00_11

theorem row_01_07_00_12 : b4RowContribution (![1, 8, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 8, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 8 + 20 = 37
    decide
  have hzsq : (∑ i, (((![1, 8, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 529 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 8^2 + 20^2 = 529
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_00_12

theorem weighted_01_07_00_12 : b4RawGapContribution ![1, 7, 0, 12] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 0, 12] = b4GapPatternWeight 7 0 12 * 0 :=
      b4GapContribution_from_row 1 7 0 12 0 row_01_07_00_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_00_12

def dvalues_01_07_00 : Fin 13 → ℕ := ![0, 0, 768, 0, 588, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_07_00

theorem dblock_01_07_00 : b4GapPatternDBlock 1 7 0 = 1356 := by
  calc
    b4GapPatternDBlock 1 7 0 = ∑ d : Fin 13, dvalues_01_07_00 d := by
      apply b4GapDBlock_of_rows 1 7 0 dvalues_01_07_00
      intro d
      fin_cases d
      · exact weighted_01_07_00_00
      · exact weighted_01_07_00_01
      · exact weighted_01_07_00_02
      · exact weighted_01_07_00_03
      · exact weighted_01_07_00_04
      · exact weighted_01_07_00_05
      · exact weighted_01_07_00_06
      · exact weighted_01_07_00_07
      · exact weighted_01_07_00_08
      · exact weighted_01_07_00_09
      · exact weighted_01_07_00_10
      · exact weighted_01_07_00_11
      · exact weighted_01_07_00_12
    _ = 1356 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_07_00

end Paper7MomentGapNumeric
