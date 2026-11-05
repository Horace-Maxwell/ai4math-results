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

theorem row_00_05_03_00 : b4RowContribution (![0, 5, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 8] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 8 = 21
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 153 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 8^2 = 153
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_00

theorem weighted_00_05_03_00 : b4RawGapContribution ![0, 5, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 0] = b4GapPatternWeight 5 3 0 * 0 :=
      b4GapContribution_from_row 0 5 3 0 0 row_00_05_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_00

theorem row_00_05_03_01 : b4RowContribution (![0, 5, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 9] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 9 = 22
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 170 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 9^2 = 170
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_01

theorem weighted_00_05_03_01 : b4RawGapContribution ![0, 5, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 1] = b4GapPatternWeight 5 3 1 * 0 :=
      b4GapContribution_from_row 0 5 3 1 0 row_00_05_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_01

theorem row_00_05_03_02 : b4RowContribution (![0, 5, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 10] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 10 = 23
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 189 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 10^2 = 189
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_02

theorem weighted_00_05_03_02 : b4RawGapContribution ![0, 5, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 2] = b4GapPatternWeight 5 3 2 * 0 :=
      b4GapContribution_from_row 0 5 3 2 0 row_00_05_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_02

theorem row_00_05_03_03 : b4RowContribution (![0, 5, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 11] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 11 = 24
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 210 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 11^2 = 210
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_03

theorem weighted_00_05_03_03 : b4RawGapContribution ![0, 5, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 3] = b4GapPatternWeight 5 3 3 * 0 :=
      b4GapContribution_from_row 0 5 3 3 0 row_00_05_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_03

def layers_00_05_03_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 6, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 27, 33, 39, 44, 48, 51, 53, 53, 51, 48, 44, 39, 33]]
#print axioms Paper7MomentGapNumeric.layers_00_05_03_04

theorem cells_00_05_03_04 : QTableValid (![0, 5, 8, 12] : Fin 4 → ℕ) layers_00_05_03_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_05_03_04

theorem valid_00_05_03_04 :
    SparseRowValid (![0, 5, 8, 12] : Fin 4 → ℕ) ({2, 8} : Finset (Fin 19)) (fun _ => layers_00_05_03_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 5, 8, 12] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 5 + 8 + 12 = 25
      decide
    have hzsq : (∑ i, (((![0, 5, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 233 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 5^2 + 8^2 + 12^2 = 233
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_05_03_04
#print axioms Paper7MomentGapNumeric.valid_00_05_03_04

def qvalues_00_05_03_04 : Fin 19 → ℕ := ![0, 0, 6, 0, 0, 0, 0, 0, 39, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_05_03_04

theorem row_00_05_03_04 : b4RowContribution (![0, 5, 8, 12] : Fin 4 → ℕ) = 45 := by
  calc
    b4RowContribution (![0, 5, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({2, 8} : Finset (Fin 19)) (fun _ => layers_00_05_03_04) :=
      sparseRow_sound (![0, 5, 8, 12] : Fin 4 → ℕ) ({2, 8} : Finset (Fin 19)) (fun _ => layers_00_05_03_04) valid_00_05_03_04
    _ = 45 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_05_03_04 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
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
        _ = 45 := by decide
#print axioms Paper7MomentGapNumeric.row_00_05_03_04

theorem weighted_00_05_03_04 : b4RawGapContribution ![0, 5, 3, 4] = 1080 := by
  calc
    b4RawGapContribution ![0, 5, 3, 4] = b4GapPatternWeight 5 3 4 * 45 :=
      b4GapContribution_from_row 0 5 3 4 45 row_00_05_03_04
    _ = 1080 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_04

theorem row_00_05_03_05 : b4RowContribution (![0, 5, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 13] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 13 = 26
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 258 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 13^2 = 258
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_05

theorem weighted_00_05_03_05 : b4RawGapContribution ![0, 5, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 5] = b4GapPatternWeight 5 3 5 * 0 :=
      b4GapContribution_from_row 0 5 3 5 0 row_00_05_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_05

def layers_00_05_03_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 6, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 27, 33, 39, 44, 48, 51, 53, 54, 54, 53, 51, 48, 44]]
#print axioms Paper7MomentGapNumeric.layers_00_05_03_06

theorem cells_00_05_03_06 : QTableValid (![0, 5, 8, 14] : Fin 4 → ℕ) layers_00_05_03_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_05_03_06

theorem valid_00_05_03_06 :
    SparseRowValid (![0, 5, 8, 14] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_05_03_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 5, 8, 14] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 0 + 5 + 8 + 14 = 27
      decide
    have hzsq : (∑ i, (((![0, 5, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 285 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 5^2 + 8^2 + 14^2 = 285
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_05_03_06
#print axioms Paper7MomentGapNumeric.valid_00_05_03_06

def qvalues_00_05_03_06 : Fin 19 → ℕ := ![0, 0, 0, 10, 0, 0, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_05_03_06

theorem row_00_05_03_06 : b4RowContribution (![0, 5, 8, 14] : Fin 4 → ℕ) = 54 := by
  calc
    b4RowContribution (![0, 5, 8, 14] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_05_03_06) :=
      sparseRow_sound (![0, 5, 8, 14] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_00_05_03_06) valid_00_05_03_06
    _ = 54 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_05_03_06 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
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
        _ = 54 := by decide
#print axioms Paper7MomentGapNumeric.row_00_05_03_06

theorem weighted_00_05_03_06 : b4RawGapContribution ![0, 5, 3, 6] = 1296 := by
  calc
    b4RawGapContribution ![0, 5, 3, 6] = b4GapPatternWeight 5 3 6 * 54 :=
      b4GapContribution_from_row 0 5 3 6 54 row_00_05_03_06
    _ = 1296 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_06

theorem row_00_05_03_07 : b4RowContribution (![0, 5, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 15] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 15 = 28
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 314 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 15^2 = 314
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_07

theorem weighted_00_05_03_07 : b4RawGapContribution ![0, 5, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 7] = b4GapPatternWeight 5 3 7 * 0 :=
      b4GapContribution_from_row 0 5 3 7 0 row_00_05_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_07

theorem row_00_05_03_08 : b4RowContribution (![0, 5, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 16 = 29
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 345 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 16^2 = 345
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_08

theorem weighted_00_05_03_08 : b4RawGapContribution ![0, 5, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 8] = b4GapPatternWeight 5 3 8 * 0 :=
      b4GapContribution_from_row 0 5 3 8 0 row_00_05_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_08

theorem row_00_05_03_09 : b4RowContribution (![0, 5, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 17 = 30
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 378 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 17^2 = 378
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_09

theorem weighted_00_05_03_09 : b4RawGapContribution ![0, 5, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 9] = b4GapPatternWeight 5 3 9 * 0 :=
      b4GapContribution_from_row 0 5 3 9 0 row_00_05_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_09

theorem row_00_05_03_10 : b4RowContribution (![0, 5, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 18 = 31
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 413 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 18^2 = 413
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_10

theorem weighted_00_05_03_10 : b4RawGapContribution ![0, 5, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 10] = b4GapPatternWeight 5 3 10 * 0 :=
      b4GapContribution_from_row 0 5 3 10 0 row_00_05_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_10

theorem row_00_05_03_11 : b4RowContribution (![0, 5, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 19 = 32
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 450 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 19^2 = 450
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_11

theorem weighted_00_05_03_11 : b4RawGapContribution ![0, 5, 3, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 11] = b4GapPatternWeight 5 3 11 * 0 :=
      b4GapContribution_from_row 0 5 3 11 0 row_00_05_03_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_11

theorem row_00_05_03_12 : b4RowContribution (![0, 5, 8, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 20 = 33
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 489 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 20^2 = 489
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_12

theorem weighted_00_05_03_12 : b4RawGapContribution ![0, 5, 3, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 12] = b4GapPatternWeight 5 3 12 * 0 :=
      b4GapContribution_from_row 0 5 3 12 0 row_00_05_03_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_12

theorem row_00_05_03_13 : b4RowContribution (![0, 5, 8, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 21] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 21 = 34
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 530 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 21^2 = 530
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_13

theorem weighted_00_05_03_13 : b4RawGapContribution ![0, 5, 3, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 13] = b4GapPatternWeight 5 3 13 * 0 :=
      b4GapContribution_from_row 0 5 3 13 0 row_00_05_03_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_13

theorem row_00_05_03_14 : b4RowContribution (![0, 5, 8, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 22 = 35
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 573 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 22^2 = 573
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_14

theorem weighted_00_05_03_14 : b4RawGapContribution ![0, 5, 3, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 14] = b4GapPatternWeight 5 3 14 * 0 :=
      b4GapContribution_from_row 0 5 3 14 0 row_00_05_03_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_14

theorem row_00_05_03_15 : b4RowContribution (![0, 5, 8, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 23 = 36
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 618 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 23^2 = 618
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_15

theorem weighted_00_05_03_15 : b4RawGapContribution ![0, 5, 3, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 15] = b4GapPatternWeight 5 3 15 * 0 :=
      b4GapContribution_from_row 0 5 3 15 0 row_00_05_03_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_15

theorem row_00_05_03_16 : b4RowContribution (![0, 5, 8, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 8, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 8 + 24 = 37
    decide
  have hzsq : (∑ i, (((![0, 5, 8, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 665 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 8^2 + 24^2 = 665
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_03_16

theorem weighted_00_05_03_16 : b4RawGapContribution ![0, 5, 3, 16] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 3, 16] = b4GapPatternWeight 5 3 16 * 0 :=
      b4GapContribution_from_row 0 5 3 16 0 row_00_05_03_16
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_03_16

def dvalues_00_05_03 : Fin 17 → ℕ := ![0, 0, 0, 0, 1080, 0, 1296, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_05_03

theorem dblock_00_05_03 : b4GapPatternDBlock 0 5 3 = 2376 := by
  calc
    b4GapPatternDBlock 0 5 3 = ∑ d : Fin 17, dvalues_00_05_03 d := by
      apply b4GapDBlock_of_rows 0 5 3 dvalues_00_05_03
      intro d
      fin_cases d
      · exact weighted_00_05_03_00
      · exact weighted_00_05_03_01
      · exact weighted_00_05_03_02
      · exact weighted_00_05_03_03
      · exact weighted_00_05_03_04
      · exact weighted_00_05_03_05
      · exact weighted_00_05_03_06
      · exact weighted_00_05_03_07
      · exact weighted_00_05_03_08
      · exact weighted_00_05_03_09
      · exact weighted_00_05_03_10
      · exact weighted_00_05_03_11
      · exact weighted_00_05_03_12
      · exact weighted_00_05_03_13
      · exact weighted_00_05_03_14
      · exact weighted_00_05_03_15
      · exact weighted_00_05_03_16
    _ = 2376 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_05_03

end Paper7MomentGapNumeric
