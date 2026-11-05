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

theorem row_02_03_04_00 : b4RowContribution (![2, 5, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 9, 9] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 9 + 9 = 25
    decide
  have hzsq : (∑ i, (((![2, 5, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 191 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 9^2 + 9^2 = 191
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_04_00

theorem weighted_02_03_04_00 : b4RawGapContribution ![2, 3, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 4, 0] = b4GapPatternWeight 3 4 0 * 0 :=
      b4GapContribution_from_row 2 3 4 0 0 row_02_03_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_04_00

theorem row_02_03_04_01 : b4RowContribution (![2, 5, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 9, 10] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 9 + 10 = 26
    decide
  have hzsq : (∑ i, (((![2, 5, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 210 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 9^2 + 10^2 = 210
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_04_01

theorem weighted_02_03_04_01 : b4RawGapContribution ![2, 3, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 4, 1] = b4GapPatternWeight 3 4 1 * 0 :=
      b4GapContribution_from_row 2 3 4 1 0 row_02_03_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_04_01

def layers_02_03_04_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 17, 18, 18, 18, 17, 15, 12, 9, 6, 3, 1, 0, 0], ![1, 4, 10, 19, 31, 46, 63, 81, 99, 117, 134, 149, 160, 166, 166, 160, 149, 134, 117]]
#print axioms Paper7MomentGapNumeric.layers_02_03_04_02

theorem cells_02_03_04_02 : QTableValid (![2, 5, 9, 11] : Fin 4 → ℕ) layers_02_03_04_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_03_04_02

theorem valid_02_03_04_02 :
    SparseRowValid (![2, 5, 9, 11] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_02_03_04_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 5, 9, 11] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 2 + 5 + 9 + 11 = 27
      decide
    have hzsq : (∑ i, (((![2, 5, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 231 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 5^2 + 9^2 + 11^2 = 231
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_03_04_02
#print axioms Paper7MomentGapNumeric.valid_02_03_04_02

def qvalues_02_03_04_02 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_03_04_02

theorem row_02_03_04_02 : b4RowContribution (![2, 5, 9, 11] : Fin 4 → ℕ) = 64 := by
  calc
    b4RowContribution (![2, 5, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_02_03_04_02) :=
      sparseRow_sound (![2, 5, 9, 11] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_02_03_04_02) valid_02_03_04_02
    _ = 64 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_03_04_02 Q := by
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
        _ = 64 := by decide
#print axioms Paper7MomentGapNumeric.row_02_03_04_02

theorem weighted_02_03_04_02 : b4RawGapContribution ![2, 3, 4, 2] = 1536 := by
  calc
    b4RawGapContribution ![2, 3, 4, 2] = b4GapPatternWeight 3 4 2 * 64 :=
      b4GapContribution_from_row 2 3 4 2 64 row_02_03_04_02
    _ = 1536 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_04_02

theorem row_02_03_04_03 : b4RowContribution (![2, 5, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 9, 12] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 9 + 12 = 28
    decide
  have hzsq : (∑ i, (((![2, 5, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 254 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 9^2 + 12^2 = 254
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_04_03

theorem weighted_02_03_04_03 : b4RawGapContribution ![2, 3, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 4, 3] = b4GapPatternWeight 3 4 3 * 0 :=
      b4GapContribution_from_row 2 3 4 3 0 row_02_03_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_04_03

def layers_02_03_04_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 17, 18, 18, 18, 17, 15, 12, 9, 6, 3, 1, 0, 0], ![1, 4, 10, 19, 31, 46, 63, 81, 99, 117, 134, 149, 161, 170, 175, 175, 170, 161, 149]]
#print axioms Paper7MomentGapNumeric.layers_02_03_04_04

theorem cells_02_03_04_04 : QTableValid (![2, 5, 9, 13] : Fin 4 → ℕ) layers_02_03_04_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_03_04_04

theorem valid_02_03_04_04 :
    SparseRowValid (![2, 5, 9, 13] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_02_03_04_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 5, 9, 13] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 2 + 5 + 9 + 13 = 29
      decide
    have hzsq : (∑ i, (((![2, 5, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 279 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 5^2 + 9^2 + 13^2 = 279
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_03_04_04
#print axioms Paper7MomentGapNumeric.valid_02_03_04_04

def qvalues_02_03_04_04 : Fin 19 → ℕ := ![0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_03_04_04

theorem row_02_03_04_04 : b4RowContribution (![2, 5, 9, 13] : Fin 4 → ℕ) = 19 := by
  calc
    b4RowContribution (![2, 5, 9, 13] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_02_03_04_04) :=
      sparseRow_sound (![2, 5, 9, 13] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_02_03_04_04) valid_02_03_04_04
    _ = 19 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_03_04_04 Q := by
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
        _ = 19 := by decide
#print axioms Paper7MomentGapNumeric.row_02_03_04_04

theorem weighted_02_03_04_04 : b4RawGapContribution ![2, 3, 4, 4] = 456 := by
  calc
    b4RawGapContribution ![2, 3, 4, 4] = b4GapPatternWeight 3 4 4 * 19 :=
      b4GapContribution_from_row 2 3 4 4 19 row_02_03_04_04
    _ = 456 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_04_04

theorem row_02_03_04_05 : b4RowContribution (![2, 5, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 9, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 9 + 14 = 30
    decide
  have hzsq : (∑ i, (((![2, 5, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 9^2 + 14^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_04_05

theorem weighted_02_03_04_05 : b4RawGapContribution ![2, 3, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 4, 5] = b4GapPatternWeight 3 4 5 * 0 :=
      b4GapContribution_from_row 2 3 4 5 0 row_02_03_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_04_05

theorem row_02_03_04_06 : b4RowContribution (![2, 5, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 9, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 9 + 15 = 31
    decide
  have hzsq : (∑ i, (((![2, 5, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 335 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 9^2 + 15^2 = 335
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_04_06

theorem weighted_02_03_04_06 : b4RawGapContribution ![2, 3, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 4, 6] = b4GapPatternWeight 3 4 6 * 0 :=
      b4GapContribution_from_row 2 3 4 6 0 row_02_03_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_04_06

theorem row_02_03_04_07 : b4RowContribution (![2, 5, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 9, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 9 + 16 = 32
    decide
  have hzsq : (∑ i, (((![2, 5, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 366 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 9^2 + 16^2 = 366
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_04_07

theorem weighted_02_03_04_07 : b4RawGapContribution ![2, 3, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 4, 7] = b4GapPatternWeight 3 4 7 * 0 :=
      b4GapContribution_from_row 2 3 4 7 0 row_02_03_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_04_07

theorem row_02_03_04_08 : b4RowContribution (![2, 5, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 9, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 9 + 17 = 33
    decide
  have hzsq : (∑ i, (((![2, 5, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 399 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 9^2 + 17^2 = 399
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_04_08

theorem weighted_02_03_04_08 : b4RawGapContribution ![2, 3, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 4, 8] = b4GapPatternWeight 3 4 8 * 0 :=
      b4GapContribution_from_row 2 3 4 8 0 row_02_03_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_04_08

theorem row_02_03_04_09 : b4RowContribution (![2, 5, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 9, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 9 + 18 = 34
    decide
  have hzsq : (∑ i, (((![2, 5, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 434 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 9^2 + 18^2 = 434
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_04_09

theorem weighted_02_03_04_09 : b4RawGapContribution ![2, 3, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 4, 9] = b4GapPatternWeight 3 4 9 * 0 :=
      b4GapContribution_from_row 2 3 4 9 0 row_02_03_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_04_09

theorem row_02_03_04_10 : b4RowContribution (![2, 5, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 9, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 9 + 19 = 35
    decide
  have hzsq : (∑ i, (((![2, 5, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 471 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 9^2 + 19^2 = 471
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_04_10

theorem weighted_02_03_04_10 : b4RawGapContribution ![2, 3, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 4, 10] = b4GapPatternWeight 3 4 10 * 0 :=
      b4GapContribution_from_row 2 3 4 10 0 row_02_03_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_04_10

theorem row_02_03_04_11 : b4RowContribution (![2, 5, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 9, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 9 + 20 = 36
    decide
  have hzsq : (∑ i, (((![2, 5, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 510 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 9^2 + 20^2 = 510
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_04_11

theorem weighted_02_03_04_11 : b4RawGapContribution ![2, 3, 4, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 4, 11] = b4GapPatternWeight 3 4 11 * 0 :=
      b4GapContribution_from_row 2 3 4 11 0 row_02_03_04_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_04_11

theorem row_02_03_04_12 : b4RowContribution (![2, 5, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 9, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 9 + 21 = 37
    decide
  have hzsq : (∑ i, (((![2, 5, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 551 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 9^2 + 21^2 = 551
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_04_12

theorem weighted_02_03_04_12 : b4RawGapContribution ![2, 3, 4, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 4, 12] = b4GapPatternWeight 3 4 12 * 0 :=
      b4GapContribution_from_row 2 3 4 12 0 row_02_03_04_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_04_12

def dvalues_02_03_04 : Fin 13 → ℕ := ![0, 0, 1536, 0, 456, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_03_04

theorem dblock_02_03_04 : b4GapPatternDBlock 2 3 4 = 1992 := by
  calc
    b4GapPatternDBlock 2 3 4 = ∑ d : Fin 13, dvalues_02_03_04 d := by
      apply b4GapDBlock_of_rows 2 3 4 dvalues_02_03_04
      intro d
      fin_cases d
      · exact weighted_02_03_04_00
      · exact weighted_02_03_04_01
      · exact weighted_02_03_04_02
      · exact weighted_02_03_04_03
      · exact weighted_02_03_04_04
      · exact weighted_02_03_04_05
      · exact weighted_02_03_04_06
      · exact weighted_02_03_04_07
      · exact weighted_02_03_04_08
      · exact weighted_02_03_04_09
      · exact weighted_02_03_04_10
      · exact weighted_02_03_04_11
      · exact weighted_02_03_04_12
    _ = 1992 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_03_04

end Paper7MomentGapNumeric
