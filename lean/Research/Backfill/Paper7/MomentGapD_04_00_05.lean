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

theorem row_04_00_05_00 : b4RowContribution (![4, 4, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 9, 9] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 9 + 9 = 26
    decide
  have hzsq : (∑ i, (((![4, 4, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 194 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 9^2 + 9^2 = 194
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_05_00

theorem weighted_04_00_05_00 : b4RawGapContribution ![4, 0, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 5, 0] = b4GapPatternWeight 0 5 0 * 0 :=
      b4GapContribution_from_row 4 0 5 0 0 row_04_00_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_05_00

theorem row_04_00_05_01 : b4RowContribution (![4, 4, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 9, 10] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 9 + 10 = 27
    decide
  have hzsq : (∑ i, (((![4, 4, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 213 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 9^2 + 10^2 = 213
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_05_01

theorem weighted_04_00_05_01 : b4RawGapContribution ![4, 0, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 5, 1] = b4GapPatternWeight 0 5 1 * 0 :=
      b4GapContribution_from_row 4 0 5 1 0 row_04_00_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_05_01

def layers_04_00_05_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 19, 22, 24, 25, 25, 24, 22, 19, 15, 10, 6, 3, 1, 0], ![1, 4, 10, 20, 35, 54, 76, 100, 125, 150, 174, 196, 214, 226, 230, 226, 214, 196, 174]]
#print axioms Paper7MomentGapNumeric.layers_04_00_05_02

theorem cells_04_00_05_02 : QTableValid (![4, 4, 9, 11] : Fin 4 → ℕ) layers_04_00_05_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_00_05_02

theorem valid_04_00_05_02 :
    SparseRowValid (![4, 4, 9, 11] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_04_00_05_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 4, 9, 11] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 4 + 4 + 9 + 11 = 28
      decide
    have hzsq : (∑ i, (((![4, 4, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 234 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 4^2 + 9^2 + 11^2 = 234
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_00_05_02
#print axioms Paper7MomentGapNumeric.valid_04_00_05_02

def qvalues_04_00_05_02 : Fin 19 → ℕ := ![0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_00_05_02

theorem row_04_00_05_02 : b4RowContribution (![4, 4, 9, 11] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![4, 4, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_04_00_05_02) :=
      sparseRow_sound (![4, 4, 9, 11] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_04_00_05_02) valid_04_00_05_02
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_00_05_02 Q := by
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
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_04_00_05_02

theorem weighted_04_00_05_02 : b4RawGapContribution ![4, 0, 5, 2] = 240 := by
  calc
    b4RawGapContribution ![4, 0, 5, 2] = b4GapPatternWeight 0 5 2 * 20 :=
      b4GapContribution_from_row 4 0 5 2 20 row_04_00_05_02
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_05_02

theorem row_04_00_05_03 : b4RowContribution (![4, 4, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 9, 12] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 9 + 12 = 29
    decide
  have hzsq : (∑ i, (((![4, 4, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 257 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 9^2 + 12^2 = 257
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_05_03

theorem weighted_04_00_05_03 : b4RawGapContribution ![4, 0, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 5, 3] = b4GapPatternWeight 0 5 3 * 0 :=
      b4GapContribution_from_row 4 0 5 3 0 row_04_00_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_05_03

def layers_04_00_05_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 19, 22, 24, 25, 25, 24, 22, 19, 15, 10, 6, 3, 1, 0], ![1, 4, 10, 20, 35, 54, 76, 100, 125, 150, 174, 196, 215, 230, 239, 242, 239, 230, 215]]
#print axioms Paper7MomentGapNumeric.layers_04_00_05_04

theorem cells_04_00_05_04 : QTableValid (![4, 4, 9, 13] : Fin 4 → ℕ) layers_04_00_05_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_00_05_04

theorem valid_04_00_05_04 :
    SparseRowValid (![4, 4, 9, 13] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_04_00_05_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 4, 9, 13] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 4 + 4 + 9 + 13 = 30
      decide
    have hzsq : (∑ i, (((![4, 4, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 282 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 4^2 + 9^2 + 13^2 = 282
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_00_05_04
#print axioms Paper7MomentGapNumeric.valid_04_00_05_04

def qvalues_04_00_05_04 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 76, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_00_05_04

theorem row_04_00_05_04 : b4RowContribution (![4, 4, 9, 13] : Fin 4 → ℕ) = 77 := by
  calc
    b4RowContribution (![4, 4, 9, 13] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_04_00_05_04) :=
      sparseRow_sound (![4, 4, 9, 13] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_04_00_05_04) valid_04_00_05_04
    _ = 77 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_00_05_04 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 77 := by decide
#print axioms Paper7MomentGapNumeric.row_04_00_05_04

theorem weighted_04_00_05_04 : b4RawGapContribution ![4, 0, 5, 4] = 924 := by
  calc
    b4RawGapContribution ![4, 0, 5, 4] = b4GapPatternWeight 0 5 4 * 77 :=
      b4GapContribution_from_row 4 0 5 4 77 row_04_00_05_04
    _ = 924 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_05_04

theorem row_04_00_05_05 : b4RowContribution (![4, 4, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 9, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 9 + 14 = 31
    decide
  have hzsq : (∑ i, (((![4, 4, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 309 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 9^2 + 14^2 = 309
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_05_05

theorem weighted_04_00_05_05 : b4RawGapContribution ![4, 0, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 5, 5] = b4GapPatternWeight 0 5 5 * 0 :=
      b4GapContribution_from_row 4 0 5 5 0 row_04_00_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_05_05

theorem row_04_00_05_06 : b4RowContribution (![4, 4, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 9, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 9 + 15 = 32
    decide
  have hzsq : (∑ i, (((![4, 4, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 338 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 9^2 + 15^2 = 338
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_05_06

theorem weighted_04_00_05_06 : b4RawGapContribution ![4, 0, 5, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 5, 6] = b4GapPatternWeight 0 5 6 * 0 :=
      b4GapContribution_from_row 4 0 5 6 0 row_04_00_05_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_05_06

theorem row_04_00_05_07 : b4RowContribution (![4, 4, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 9, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 9 + 16 = 33
    decide
  have hzsq : (∑ i, (((![4, 4, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 369 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 9^2 + 16^2 = 369
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_05_07

theorem weighted_04_00_05_07 : b4RawGapContribution ![4, 0, 5, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 5, 7] = b4GapPatternWeight 0 5 7 * 0 :=
      b4GapContribution_from_row 4 0 5 7 0 row_04_00_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_05_07

theorem row_04_00_05_08 : b4RowContribution (![4, 4, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 9, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 9 + 17 = 34
    decide
  have hzsq : (∑ i, (((![4, 4, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 402 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 9^2 + 17^2 = 402
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_05_08

theorem weighted_04_00_05_08 : b4RawGapContribution ![4, 0, 5, 8] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 5, 8] = b4GapPatternWeight 0 5 8 * 0 :=
      b4GapContribution_from_row 4 0 5 8 0 row_04_00_05_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_05_08

theorem row_04_00_05_09 : b4RowContribution (![4, 4, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 9, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 9 + 18 = 35
    decide
  have hzsq : (∑ i, (((![4, 4, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 437 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 9^2 + 18^2 = 437
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_05_09

theorem weighted_04_00_05_09 : b4RawGapContribution ![4, 0, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 5, 9] = b4GapPatternWeight 0 5 9 * 0 :=
      b4GapContribution_from_row 4 0 5 9 0 row_04_00_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_05_09

theorem row_04_00_05_10 : b4RowContribution (![4, 4, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 9, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 9 + 19 = 36
    decide
  have hzsq : (∑ i, (((![4, 4, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 474 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 9^2 + 19^2 = 474
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_05_10

theorem weighted_04_00_05_10 : b4RawGapContribution ![4, 0, 5, 10] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 5, 10] = b4GapPatternWeight 0 5 10 * 0 :=
      b4GapContribution_from_row 4 0 5 10 0 row_04_00_05_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_05_10

theorem row_04_00_05_11 : b4RowContribution (![4, 4, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 9, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 9 + 20 = 37
    decide
  have hzsq : (∑ i, (((![4, 4, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 513 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 9^2 + 20^2 = 513
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_05_11

theorem weighted_04_00_05_11 : b4RawGapContribution ![4, 0, 5, 11] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 5, 11] = b4GapPatternWeight 0 5 11 * 0 :=
      b4GapContribution_from_row 4 0 5 11 0 row_04_00_05_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_05_11

def dvalues_04_00_05 : Fin 12 → ℕ := ![0, 0, 240, 0, 924, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_00_05

theorem dblock_04_00_05 : b4GapPatternDBlock 4 0 5 = 1164 := by
  calc
    b4GapPatternDBlock 4 0 5 = ∑ d : Fin 12, dvalues_04_00_05 d := by
      apply b4GapDBlock_of_rows 4 0 5 dvalues_04_00_05
      intro d
      fin_cases d
      · exact weighted_04_00_05_00
      · exact weighted_04_00_05_01
      · exact weighted_04_00_05_02
      · exact weighted_04_00_05_03
      · exact weighted_04_00_05_04
      · exact weighted_04_00_05_05
      · exact weighted_04_00_05_06
      · exact weighted_04_00_05_07
      · exact weighted_04_00_05_08
      · exact weighted_04_00_05_09
      · exact weighted_04_00_05_10
      · exact weighted_04_00_05_11
    _ = 1164 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_00_05

end Paper7MomentGapNumeric
