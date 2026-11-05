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

theorem row_02_00_08_00 : b4RowContribution (![2, 2, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 10, 10] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 10 + 10 = 24
    decide
  have hzsq : (∑ i, (((![2, 2, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 208 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 10^2 + 10^2 = 208
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_08_00

theorem weighted_02_00_08_00 : b4RawGapContribution ![2, 0, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 8, 0] = b4GapPatternWeight 0 8 0 * 0 :=
      b4GapContribution_from_row 2 0 8 0 0 row_02_00_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_08_00

def layers_02_00_08_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 9, 9, 9, 9, 9, 8, 6, 3, 1, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 36, 45, 54, 63, 72, 81, 89, 94, 94, 89, 81, 72, 63, 54]]
#print axioms Paper7MomentGapNumeric.layers_02_00_08_01

theorem cells_02_00_08_01 : QTableValid (![2, 2, 10, 11] : Fin 4 → ℕ) layers_02_00_08_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_08_01

theorem valid_02_00_08_01 :
    SparseRowValid (![2, 2, 10, 11] : Fin 4 → ℕ) ({4, 10} : Finset (Fin 19)) (fun _ => layers_02_00_08_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 10, 11] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 10 + 11 = 25
      decide
    have hzsq : (∑ i, (((![2, 2, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 229 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 10^2 + 11^2 = 229
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_08_01
#print axioms Paper7MomentGapNumeric.valid_02_00_08_01

def qvalues_02_00_08_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 81, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_08_01

theorem row_02_00_08_01 : b4RowContribution (![2, 2, 10, 11] : Fin 4 → ℕ) = 108 := by
  calc
    b4RowContribution (![2, 2, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({4, 10} : Finset (Fin 19)) (fun _ => layers_02_00_08_01) :=
      sparseRow_sound (![2, 2, 10, 11] : Fin 4 → ℕ) ({4, 10} : Finset (Fin 19)) (fun _ => layers_02_00_08_01) valid_02_00_08_01
    _ = 108 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_08_01 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 108 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_08_01

theorem weighted_02_00_08_01 : b4RawGapContribution ![2, 0, 8, 1] = 1296 := by
  calc
    b4RawGapContribution ![2, 0, 8, 1] = b4GapPatternWeight 0 8 1 * 108 :=
      b4GapContribution_from_row 2 0 8 1 108 row_02_00_08_01
    _ = 1296 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_08_01

theorem row_02_00_08_02 : b4RowContribution (![2, 2, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 10, 12] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 10 + 12 = 26
    decide
  have hzsq : (∑ i, (((![2, 2, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 252 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 10^2 + 12^2 = 252
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_08_02

theorem weighted_02_00_08_02 : b4RawGapContribution ![2, 0, 8, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 8, 2] = b4GapPatternWeight 0 8 2 * 0 :=
      b4GapContribution_from_row 2 0 8 2 0 row_02_00_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_08_02

def layers_02_00_08_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 9, 9, 9, 9, 9, 8, 6, 3, 1, 0, 0, 0, 0], ![1, 4, 10, 18, 27, 36, 45, 54, 63, 72, 81, 89, 95, 98, 98, 95, 89, 81, 72]]
#print axioms Paper7MomentGapNumeric.layers_02_00_08_03

theorem cells_02_00_08_03 : QTableValid (![2, 2, 10, 13] : Fin 4 → ℕ) layers_02_00_08_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_08_03

theorem valid_02_00_08_03 :
    SparseRowValid (![2, 2, 10, 13] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_02_00_08_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 10, 13] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 10 + 13 = 27
      decide
    have hzsq : (∑ i, (((![2, 2, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 277 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 10^2 + 13^2 = 277
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_08_03
#print axioms Paper7MomentGapNumeric.valid_02_00_08_03

def qvalues_02_00_08_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_08_03

theorem row_02_00_08_03 : b4RowContribution (![2, 2, 10, 13] : Fin 4 → ℕ) = 54 := by
  calc
    b4RowContribution (![2, 2, 10, 13] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_02_00_08_03) :=
      sparseRow_sound (![2, 2, 10, 13] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_02_00_08_03) valid_02_00_08_03
    _ = 54 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_08_03 Q := by
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
        _ = 54 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_08_03

theorem weighted_02_00_08_03 : b4RawGapContribution ![2, 0, 8, 3] = 648 := by
  calc
    b4RawGapContribution ![2, 0, 8, 3] = b4GapPatternWeight 0 8 3 * 54 :=
      b4GapContribution_from_row 2 0 8 3 54 row_02_00_08_03
    _ = 648 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_08_03

theorem row_02_00_08_04 : b4RowContribution (![2, 2, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 10, 14] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 10 + 14 = 28
    decide
  have hzsq : (∑ i, (((![2, 2, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 304 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 10^2 + 14^2 = 304
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_08_04

theorem weighted_02_00_08_04 : b4RawGapContribution ![2, 0, 8, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 8, 4] = b4GapPatternWeight 0 8 4 * 0 :=
      b4GapContribution_from_row 2 0 8 4 0 row_02_00_08_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_08_04

theorem row_02_00_08_05 : b4RowContribution (![2, 2, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 10, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 10 + 15 = 29
    decide
  have hzsq : (∑ i, (((![2, 2, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 333 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 10^2 + 15^2 = 333
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_08_05

theorem weighted_02_00_08_05 : b4RawGapContribution ![2, 0, 8, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 8, 5] = b4GapPatternWeight 0 8 5 * 0 :=
      b4GapContribution_from_row 2 0 8 5 0 row_02_00_08_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_08_05

theorem row_02_00_08_06 : b4RowContribution (![2, 2, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 10, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 10 + 16 = 30
    decide
  have hzsq : (∑ i, (((![2, 2, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 364 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 10^2 + 16^2 = 364
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_08_06

theorem weighted_02_00_08_06 : b4RawGapContribution ![2, 0, 8, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 8, 6] = b4GapPatternWeight 0 8 6 * 0 :=
      b4GapContribution_from_row 2 0 8 6 0 row_02_00_08_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_08_06

theorem row_02_00_08_07 : b4RowContribution (![2, 2, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 10, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 10 + 17 = 31
    decide
  have hzsq : (∑ i, (((![2, 2, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 397 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 10^2 + 17^2 = 397
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_08_07

theorem weighted_02_00_08_07 : b4RawGapContribution ![2, 0, 8, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 8, 7] = b4GapPatternWeight 0 8 7 * 0 :=
      b4GapContribution_from_row 2 0 8 7 0 row_02_00_08_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_08_07

theorem row_02_00_08_08 : b4RowContribution (![2, 2, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 10, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 10 + 18 = 32
    decide
  have hzsq : (∑ i, (((![2, 2, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 432 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 10^2 + 18^2 = 432
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_08_08

theorem weighted_02_00_08_08 : b4RawGapContribution ![2, 0, 8, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 8, 8] = b4GapPatternWeight 0 8 8 * 0 :=
      b4GapContribution_from_row 2 0 8 8 0 row_02_00_08_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_08_08

theorem row_02_00_08_09 : b4RowContribution (![2, 2, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 10, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 10 + 19 = 33
    decide
  have hzsq : (∑ i, (((![2, 2, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 469 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 10^2 + 19^2 = 469
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_08_09

theorem weighted_02_00_08_09 : b4RawGapContribution ![2, 0, 8, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 8, 9] = b4GapPatternWeight 0 8 9 * 0 :=
      b4GapContribution_from_row 2 0 8 9 0 row_02_00_08_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_08_09

theorem row_02_00_08_10 : b4RowContribution (![2, 2, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 10, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 10 + 20 = 34
    decide
  have hzsq : (∑ i, (((![2, 2, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 508 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 10^2 + 20^2 = 508
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_08_10

theorem weighted_02_00_08_10 : b4RawGapContribution ![2, 0, 8, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 8, 10] = b4GapPatternWeight 0 8 10 * 0 :=
      b4GapContribution_from_row 2 0 8 10 0 row_02_00_08_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_08_10

theorem row_02_00_08_11 : b4RowContribution (![2, 2, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 10, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 10 + 21 = 35
    decide
  have hzsq : (∑ i, (((![2, 2, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 549 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 10^2 + 21^2 = 549
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_08_11

theorem weighted_02_00_08_11 : b4RawGapContribution ![2, 0, 8, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 8, 11] = b4GapPatternWeight 0 8 11 * 0 :=
      b4GapContribution_from_row 2 0 8 11 0 row_02_00_08_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_08_11

theorem row_02_00_08_12 : b4RowContribution (![2, 2, 10, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 10, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 10 + 22 = 36
    decide
  have hzsq : (∑ i, (((![2, 2, 10, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 592 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 10^2 + 22^2 = 592
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_08_12

theorem weighted_02_00_08_12 : b4RawGapContribution ![2, 0, 8, 12] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 8, 12] = b4GapPatternWeight 0 8 12 * 0 :=
      b4GapContribution_from_row 2 0 8 12 0 row_02_00_08_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_08_12

theorem row_02_00_08_13 : b4RowContribution (![2, 2, 10, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 10, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 10 + 23 = 37
    decide
  have hzsq : (∑ i, (((![2, 2, 10, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 637 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 10^2 + 23^2 = 637
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_08_13

theorem weighted_02_00_08_13 : b4RawGapContribution ![2, 0, 8, 13] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 8, 13] = b4GapPatternWeight 0 8 13 * 0 :=
      b4GapContribution_from_row 2 0 8 13 0 row_02_00_08_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_08_13

def dvalues_02_00_08 : Fin 14 → ℕ := ![0, 1296, 0, 648, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_00_08

theorem dblock_02_00_08 : b4GapPatternDBlock 2 0 8 = 1944 := by
  calc
    b4GapPatternDBlock 2 0 8 = ∑ d : Fin 14, dvalues_02_00_08 d := by
      apply b4GapDBlock_of_rows 2 0 8 dvalues_02_00_08
      intro d
      fin_cases d
      · exact weighted_02_00_08_00
      · exact weighted_02_00_08_01
      · exact weighted_02_00_08_02
      · exact weighted_02_00_08_03
      · exact weighted_02_00_08_04
      · exact weighted_02_00_08_05
      · exact weighted_02_00_08_06
      · exact weighted_02_00_08_07
      · exact weighted_02_00_08_08
      · exact weighted_02_00_08_09
      · exact weighted_02_00_08_10
      · exact weighted_02_00_08_11
      · exact weighted_02_00_08_12
      · exact weighted_02_00_08_13
    _ = 1944 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_00_08

end Paper7MomentGapNumeric
