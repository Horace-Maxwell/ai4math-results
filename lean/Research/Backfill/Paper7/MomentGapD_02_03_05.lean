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

def layers_02_03_05_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 17, 18, 18, 18, 18, 17, 15, 12, 9, 6, 3, 1, 0], ![1, 4, 10, 19, 31, 46, 63, 81, 99, 117, 135, 151, 163, 169, 169, 163, 151, 135, 117]]
#print axioms Paper7MomentGapNumeric.layers_02_03_05_00

theorem cells_02_03_05_00 : QTableValid (![2, 5, 10, 10] : Fin 4 → ℕ) layers_02_03_05_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_03_05_00

theorem valid_02_03_05_00 :
    SparseRowValid (![2, 5, 10, 10] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_02_03_05_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 5, 10, 10] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 2 + 5 + 10 + 10 = 27
      decide
    have hzsq : (∑ i, (((![2, 5, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 229 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 5^2 + 10^2 + 10^2 = 229
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_03_05_00
#print axioms Paper7MomentGapNumeric.valid_02_03_05_00

def qvalues_02_03_05_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_03_05_00

theorem row_02_03_05_00 : b4RowContribution (![2, 5, 10, 10] : Fin 4 → ℕ) = 81 := by
  calc
    b4RowContribution (![2, 5, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_02_03_05_00) :=
      sparseRow_sound (![2, 5, 10, 10] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_02_03_05_00) valid_02_03_05_00
    _ = 81 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_03_05_00 Q := by
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
        _ = 81 := by decide
#print axioms Paper7MomentGapNumeric.row_02_03_05_00

theorem weighted_02_03_05_00 : b4RawGapContribution ![2, 3, 5, 0] = 972 := by
  calc
    b4RawGapContribution ![2, 3, 5, 0] = b4GapPatternWeight 3 5 0 * 81 :=
      b4GapContribution_from_row 2 3 5 0 81 row_02_03_05_00
    _ = 972 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_05_00

theorem row_02_03_05_01 : b4RowContribution (![2, 5, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 10, 11] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 10 + 11 = 28
    decide
  have hzsq : (∑ i, (((![2, 5, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 250 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 10^2 + 11^2 = 250
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_05_01

theorem weighted_02_03_05_01 : b4RawGapContribution ![2, 3, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 5, 1] = b4GapPatternWeight 3 5 1 * 0 :=
      b4GapContribution_from_row 2 3 5 1 0 row_02_03_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_05_01

def layers_02_03_05_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 17, 18, 18, 18, 18, 17, 15, 12, 9, 6, 3, 1, 0], ![1, 4, 10, 19, 31, 46, 63, 81, 99, 117, 135, 152, 167, 178, 184, 184, 178, 167, 152]]
#print axioms Paper7MomentGapNumeric.layers_02_03_05_02

theorem cells_02_03_05_02 : QTableValid (![2, 5, 10, 12] : Fin 4 → ℕ) layers_02_03_05_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_03_05_02

theorem valid_02_03_05_02 :
    SparseRowValid (![2, 5, 10, 12] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_02_03_05_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 5, 10, 12] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 2 + 5 + 10 + 12 = 29
      decide
    have hzsq : (∑ i, (((![2, 5, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 273 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 5^2 + 10^2 + 12^2 = 273
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_03_05_02
#print axioms Paper7MomentGapNumeric.valid_02_03_05_02

def qvalues_02_03_05_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_03_05_02

theorem row_02_03_05_02 : b4RowContribution (![2, 5, 10, 12] : Fin 4 → ℕ) = 63 := by
  calc
    b4RowContribution (![2, 5, 10, 12] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_02_03_05_02) :=
      sparseRow_sound (![2, 5, 10, 12] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_02_03_05_02) valid_02_03_05_02
    _ = 63 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_03_05_02 Q := by
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
        _ = 63 := by decide
#print axioms Paper7MomentGapNumeric.row_02_03_05_02

theorem weighted_02_03_05_02 : b4RawGapContribution ![2, 3, 5, 2] = 1512 := by
  calc
    b4RawGapContribution ![2, 3, 5, 2] = b4GapPatternWeight 3 5 2 * 63 :=
      b4GapContribution_from_row 2 3 5 2 63 row_02_03_05_02
    _ = 1512 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_05_02

theorem row_02_03_05_03 : b4RowContribution (![2, 5, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 10, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 10 + 13 = 30
    decide
  have hzsq : (∑ i, (((![2, 5, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 298 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 10^2 + 13^2 = 298
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_05_03

theorem weighted_02_03_05_03 : b4RawGapContribution ![2, 3, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 5, 3] = b4GapPatternWeight 3 5 3 * 0 :=
      b4GapContribution_from_row 2 3 5 3 0 row_02_03_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_05_03

theorem row_02_03_05_04 : b4RowContribution (![2, 5, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 10, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 10 + 14 = 31
    decide
  have hzsq : (∑ i, (((![2, 5, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 10^2 + 14^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_05_04

theorem weighted_02_03_05_04 : b4RawGapContribution ![2, 3, 5, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 5, 4] = b4GapPatternWeight 3 5 4 * 0 :=
      b4GapContribution_from_row 2 3 5 4 0 row_02_03_05_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_05_04

theorem row_02_03_05_05 : b4RowContribution (![2, 5, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 10, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 10 + 15 = 32
    decide
  have hzsq : (∑ i, (((![2, 5, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 354 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 10^2 + 15^2 = 354
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_05_05

theorem weighted_02_03_05_05 : b4RawGapContribution ![2, 3, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 5, 5] = b4GapPatternWeight 3 5 5 * 0 :=
      b4GapContribution_from_row 2 3 5 5 0 row_02_03_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_05_05

theorem row_02_03_05_06 : b4RowContribution (![2, 5, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 10, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 10 + 16 = 33
    decide
  have hzsq : (∑ i, (((![2, 5, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 385 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 10^2 + 16^2 = 385
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_05_06

theorem weighted_02_03_05_06 : b4RawGapContribution ![2, 3, 5, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 5, 6] = b4GapPatternWeight 3 5 6 * 0 :=
      b4GapContribution_from_row 2 3 5 6 0 row_02_03_05_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_05_06

theorem row_02_03_05_07 : b4RowContribution (![2, 5, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 10, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 10 + 17 = 34
    decide
  have hzsq : (∑ i, (((![2, 5, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 418 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 10^2 + 17^2 = 418
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_05_07

theorem weighted_02_03_05_07 : b4RawGapContribution ![2, 3, 5, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 5, 7] = b4GapPatternWeight 3 5 7 * 0 :=
      b4GapContribution_from_row 2 3 5 7 0 row_02_03_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_05_07

theorem row_02_03_05_08 : b4RowContribution (![2, 5, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 10, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 10 + 18 = 35
    decide
  have hzsq : (∑ i, (((![2, 5, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 453 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 10^2 + 18^2 = 453
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_05_08

theorem weighted_02_03_05_08 : b4RawGapContribution ![2, 3, 5, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 5, 8] = b4GapPatternWeight 3 5 8 * 0 :=
      b4GapContribution_from_row 2 3 5 8 0 row_02_03_05_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_05_08

theorem row_02_03_05_09 : b4RowContribution (![2, 5, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 10, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 10 + 19 = 36
    decide
  have hzsq : (∑ i, (((![2, 5, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 490 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 10^2 + 19^2 = 490
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_05_09

theorem weighted_02_03_05_09 : b4RawGapContribution ![2, 3, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 5, 9] = b4GapPatternWeight 3 5 9 * 0 :=
      b4GapContribution_from_row 2 3 5 9 0 row_02_03_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_05_09

theorem row_02_03_05_10 : b4RowContribution (![2, 5, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 10, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 10 + 20 = 37
    decide
  have hzsq : (∑ i, (((![2, 5, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 529 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 10^2 + 20^2 = 529
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_05_10

theorem weighted_02_03_05_10 : b4RawGapContribution ![2, 3, 5, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 5, 10] = b4GapPatternWeight 3 5 10 * 0 :=
      b4GapContribution_from_row 2 3 5 10 0 row_02_03_05_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_05_10

def dvalues_02_03_05 : Fin 11 → ℕ := ![972, 0, 1512, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_03_05

theorem dblock_02_03_05 : b4GapPatternDBlock 2 3 5 = 2484 := by
  calc
    b4GapPatternDBlock 2 3 5 = ∑ d : Fin 11, dvalues_02_03_05 d := by
      apply b4GapDBlock_of_rows 2 3 5 dvalues_02_03_05
      intro d
      fin_cases d
      · exact weighted_02_03_05_00
      · exact weighted_02_03_05_01
      · exact weighted_02_03_05_02
      · exact weighted_02_03_05_03
      · exact weighted_02_03_05_04
      · exact weighted_02_03_05_05
      · exact weighted_02_03_05_06
      · exact weighted_02_03_05_07
      · exact weighted_02_03_05_08
      · exact weighted_02_03_05_09
      · exact weighted_02_03_05_10
    _ = 2484 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_03_05

end Paper7MomentGapNumeric
