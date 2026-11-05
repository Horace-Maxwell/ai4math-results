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

theorem row_03_05_00_00 : b4RowContribution (![3, 8, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 8, 8] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 8 + 8 = 27
    decide
  have hzsq : (∑ i, (((![3, 8, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 201 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 8^2 + 8^2 = 201
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_00_00

theorem weighted_03_05_00_00 : b4RawGapContribution ![3, 5, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 0, 0] = b4GapPatternWeight 5 0 0 * 0 :=
      b4GapContribution_from_row 3 5 0 0 0 row_03_05_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_00_00

theorem row_03_05_00_01 : b4RowContribution (![3, 8, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 8, 9] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 8 + 9 = 28
    decide
  have hzsq : (∑ i, (((![3, 8, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 218 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 8^2 + 9^2 = 218
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_00_01

theorem weighted_03_05_00_01 : b4RawGapContribution ![3, 5, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 0, 1] = b4GapPatternWeight 5 0 1 * 0 :=
      b4GapContribution_from_row 3 5 0 1 0 row_03_05_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_00_01

def layers_03_05_00_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 30, 32, 32, 30, 26, 22, 18, 14, 10, 6, 3], ![1, 4, 10, 20, 34, 52, 74, 100, 130, 162, 194, 223, 246, 262, 270, 270, 262, 246, 223]]
#print axioms Paper7MomentGapNumeric.layers_03_05_00_02

theorem cells_03_05_00_02 : QTableValid (![3, 8, 8, 10] : Fin 4 → ℕ) layers_03_05_00_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_05_00_02

theorem valid_03_05_00_02 :
    SparseRowValid (![3, 8, 8, 10] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_03_05_00_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 8, 8, 10] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 3 + 8 + 8 + 10 = 29
      decide
    have hzsq : (∑ i, (((![3, 8, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 237 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 8^2 + 8^2 + 10^2 = 237
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_05_00_02
#print axioms Paper7MomentGapNumeric.valid_03_05_00_02

def qvalues_03_05_00_02 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_05_00_02

theorem row_03_05_00_02 : b4RowContribution (![3, 8, 8, 10] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![3, 8, 8, 10] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_03_05_00_02) :=
      sparseRow_sound (![3, 8, 8, 10] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_03_05_00_02) valid_03_05_00_02
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_05_00_02 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 1 := by decide
#print axioms Paper7MomentGapNumeric.row_03_05_00_02

theorem weighted_03_05_00_02 : b4RawGapContribution ![3, 5, 0, 2] = 12 := by
  calc
    b4RawGapContribution ![3, 5, 0, 2] = b4GapPatternWeight 5 0 2 * 1 :=
      b4GapContribution_from_row 3 5 0 2 1 row_03_05_00_02
    _ = 12 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_00_02

theorem row_03_05_00_03 : b4RowContribution (![3, 8, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 8, 11] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 8 + 11 = 30
    decide
  have hzsq : (∑ i, (((![3, 8, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 258 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 8^2 + 11^2 = 258
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_00_03

theorem weighted_03_05_00_03 : b4RawGapContribution ![3, 5, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 0, 3] = b4GapPatternWeight 5 0 3 * 0 :=
      b4GapContribution_from_row 3 5 0 3 0 row_03_05_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_00_03

def layers_03_05_00_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 30, 32, 32, 30, 26, 22, 18, 14, 10, 6, 3], ![1, 4, 10, 20, 34, 52, 74, 100, 130, 162, 194, 224, 250, 271, 286, 294, 294, 286, 271]]
#print axioms Paper7MomentGapNumeric.layers_03_05_00_04

theorem cells_03_05_00_04 : QTableValid (![3, 8, 8, 12] : Fin 4 → ℕ) layers_03_05_00_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_05_00_04

theorem valid_03_05_00_04 :
    SparseRowValid (![3, 8, 8, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_05_00_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 8, 8, 12] : Fin 4 → ℕ) i) = 31 := by
      rw [Fin.sum_univ_four]
      change 3 + 8 + 8 + 12 = 31
      decide
    have hzsq : (∑ i, (((![3, 8, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 281 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 8^2 + 8^2 + 12^2 = 281
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_05_00_04
#print axioms Paper7MomentGapNumeric.valid_03_05_00_04

def qvalues_03_05_00_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_05_00_04

theorem row_03_05_00_04 : b4RowContribution (![3, 8, 8, 12] : Fin 4 → ℕ) = 52 := by
  calc
    b4RowContribution (![3, 8, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_03_05_00_04) :=
      sparseRow_sound (![3, 8, 8, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_03_05_00_04) valid_03_05_00_04
    _ = 52 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_05_00_04 Q := by
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
        _ = 52 := by decide
#print axioms Paper7MomentGapNumeric.row_03_05_00_04

theorem weighted_03_05_00_04 : b4RawGapContribution ![3, 5, 0, 4] = 624 := by
  calc
    b4RawGapContribution ![3, 5, 0, 4] = b4GapPatternWeight 5 0 4 * 52 :=
      b4GapContribution_from_row 3 5 0 4 52 row_03_05_00_04
    _ = 624 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_00_04

theorem row_03_05_00_05 : b4RowContribution (![3, 8, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 8, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 8 + 13 = 32
    decide
  have hzsq : (∑ i, (((![3, 8, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 8^2 + 13^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_00_05

theorem weighted_03_05_00_05 : b4RawGapContribution ![3, 5, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 0, 5] = b4GapPatternWeight 5 0 5 * 0 :=
      b4GapContribution_from_row 3 5 0 5 0 row_03_05_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_00_05

theorem row_03_05_00_06 : b4RowContribution (![3, 8, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 8, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 8 + 14 = 33
    decide
  have hzsq : (∑ i, (((![3, 8, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 333 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 8^2 + 14^2 = 333
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_00_06

theorem weighted_03_05_00_06 : b4RawGapContribution ![3, 5, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 0, 6] = b4GapPatternWeight 5 0 6 * 0 :=
      b4GapContribution_from_row 3 5 0 6 0 row_03_05_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_00_06

theorem row_03_05_00_07 : b4RowContribution (![3, 8, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 8, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 8 + 15 = 34
    decide
  have hzsq : (∑ i, (((![3, 8, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 362 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 8^2 + 15^2 = 362
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_00_07

theorem weighted_03_05_00_07 : b4RawGapContribution ![3, 5, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 0, 7] = b4GapPatternWeight 5 0 7 * 0 :=
      b4GapContribution_from_row 3 5 0 7 0 row_03_05_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_00_07

theorem row_03_05_00_08 : b4RowContribution (![3, 8, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 8, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 8 + 16 = 35
    decide
  have hzsq : (∑ i, (((![3, 8, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 393 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 8^2 + 16^2 = 393
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_00_08

theorem weighted_03_05_00_08 : b4RawGapContribution ![3, 5, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 0, 8] = b4GapPatternWeight 5 0 8 * 0 :=
      b4GapContribution_from_row 3 5 0 8 0 row_03_05_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_00_08

theorem row_03_05_00_09 : b4RowContribution (![3, 8, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 8, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 8 + 17 = 36
    decide
  have hzsq : (∑ i, (((![3, 8, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 426 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 8^2 + 17^2 = 426
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_00_09

theorem weighted_03_05_00_09 : b4RawGapContribution ![3, 5, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 0, 9] = b4GapPatternWeight 5 0 9 * 0 :=
      b4GapContribution_from_row 3 5 0 9 0 row_03_05_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_00_09

theorem row_03_05_00_10 : b4RowContribution (![3, 8, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 8, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 8 + 18 = 37
    decide
  have hzsq : (∑ i, (((![3, 8, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 461 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 8^2 + 18^2 = 461
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_00_10

theorem weighted_03_05_00_10 : b4RawGapContribution ![3, 5, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 0, 10] = b4GapPatternWeight 5 0 10 * 0 :=
      b4GapContribution_from_row 3 5 0 10 0 row_03_05_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_00_10

def dvalues_03_05_00 : Fin 11 → ℕ := ![0, 0, 12, 0, 624, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_05_00

theorem dblock_03_05_00 : b4GapPatternDBlock 3 5 0 = 636 := by
  calc
    b4GapPatternDBlock 3 5 0 = ∑ d : Fin 11, dvalues_03_05_00 d := by
      apply b4GapDBlock_of_rows 3 5 0 dvalues_03_05_00
      intro d
      fin_cases d
      · exact weighted_03_05_00_00
      · exact weighted_03_05_00_01
      · exact weighted_03_05_00_02
      · exact weighted_03_05_00_03
      · exact weighted_03_05_00_04
      · exact weighted_03_05_00_05
      · exact weighted_03_05_00_06
      · exact weighted_03_05_00_07
      · exact weighted_03_05_00_08
      · exact weighted_03_05_00_09
      · exact weighted_03_05_00_10
    _ = 636 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_05_00

end Paper7MomentGapNumeric
