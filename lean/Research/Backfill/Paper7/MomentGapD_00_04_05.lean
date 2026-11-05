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

theorem row_00_04_05_00 : b4RowContribution (![0, 4, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 9, 9] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 9 + 9 = 22
    decide
  have hzsq : (∑ i, (((![0, 4, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 178 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 9^2 + 9^2 = 178
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_05_00

theorem weighted_00_04_05_00 : b4RawGapContribution ![0, 4, 5, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 5, 0] = b4GapPatternWeight 4 5 0 * 0 :=
      b4GapContribution_from_row 0 4 5 0 0 row_00_04_05_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_00

theorem row_00_04_05_01 : b4RowContribution (![0, 4, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 9, 10] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 9 + 10 = 23
    decide
  have hzsq : (∑ i, (((![0, 4, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 197 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 9^2 + 10^2 = 197
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_05_01

theorem weighted_00_04_05_01 : b4RawGapContribution ![0, 4, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 5, 1] = b4GapPatternWeight 4 5 1 * 0 :=
      b4GapContribution_from_row 0 4 5 1 0 row_00_04_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_01

def layers_00_04_05_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 35, 40, 44, 47, 48, 47, 44, 40, 35, 30, 25]]
#print axioms Paper7MomentGapNumeric.layers_00_04_05_02

theorem cells_00_04_05_02 : QTableValid (![0, 4, 9, 11] : Fin 4 → ℕ) layers_00_04_05_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_05_02

theorem valid_00_04_05_02 :
    SparseRowValid (![0, 4, 9, 11] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_04_05_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 9, 11] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 9 + 11 = 24
      decide
    have hzsq : (∑ i, (((![0, 4, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 218 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 9^2 + 11^2 = 218
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_05_02
#print axioms Paper7MomentGapNumeric.valid_00_04_05_02

def qvalues_00_04_05_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_05_02

theorem row_00_04_05_02 : b4RowContribution (![0, 4, 9, 11] : Fin 4 → ℕ) = 47 := by
  calc
    b4RowContribution (![0, 4, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({11} : Finset (Fin 19)) (fun _ => layers_00_04_05_02) :=
      sparseRow_sound (![0, 4, 9, 11] : Fin 4 → ℕ) ({11} : Finset (Fin 19)) (fun _ => layers_00_04_05_02) valid_00_04_05_02
    _ = 47 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_05_02 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 47 := by decide
#print axioms Paper7MomentGapNumeric.row_00_04_05_02

theorem weighted_00_04_05_02 : b4RawGapContribution ![0, 4, 5, 2] = 1128 := by
  calc
    b4RawGapContribution ![0, 4, 5, 2] = b4GapPatternWeight 4 5 2 * 47 :=
      b4GapContribution_from_row 0 4 5 2 47 row_00_04_05_02
    _ = 1128 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_02

def layers_00_04_05_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 35, 40, 44, 47, 49, 49, 47, 44, 40, 35, 30]]
#print axioms Paper7MomentGapNumeric.layers_00_04_05_03

theorem cells_00_04_05_03 : QTableValid (![0, 4, 9, 12] : Fin 4 → ℕ) layers_00_04_05_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_05_03

theorem valid_00_04_05_03 :
    SparseRowValid (![0, 4, 9, 12] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_00_04_05_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 9, 12] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 9 + 12 = 25
      decide
    have hzsq : (∑ i, (((![0, 4, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 241 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 9^2 + 12^2 = 241
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_05_03
#print axioms Paper7MomentGapNumeric.valid_00_04_05_03

def qvalues_00_04_05_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_05_03

theorem row_00_04_05_03 : b4RowContribution (![0, 4, 9, 12] : Fin 4 → ℕ) = 15 := by
  calc
    b4RowContribution (![0, 4, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_00_04_05_03) :=
      sparseRow_sound (![0, 4, 9, 12] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_00_04_05_03) valid_00_04_05_03
    _ = 15 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_05_03 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 15 := by decide
#print axioms Paper7MomentGapNumeric.row_00_04_05_03

theorem weighted_00_04_05_03 : b4RawGapContribution ![0, 4, 5, 3] = 360 := by
  calc
    b4RawGapContribution ![0, 4, 5, 3] = b4GapPatternWeight 4 5 3 * 15 :=
      b4GapContribution_from_row 0 4 5 3 15 row_00_04_05_03
    _ = 360 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_03

theorem row_00_04_05_04 : b4RowContribution (![0, 4, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 9, 13] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 9 + 13 = 26
    decide
  have hzsq : (∑ i, (((![0, 4, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 266 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 9^2 + 13^2 = 266
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_05_04

theorem weighted_00_04_05_04 : b4RawGapContribution ![0, 4, 5, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 5, 4] = b4GapPatternWeight 4 5 4 * 0 :=
      b4GapContribution_from_row 0 4 5 4 0 row_00_04_05_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_04

theorem row_00_04_05_05 : b4RowContribution (![0, 4, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 9, 14] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 9 + 14 = 27
    decide
  have hzsq : (∑ i, (((![0, 4, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 293 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 9^2 + 14^2 = 293
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_05_05

theorem weighted_00_04_05_05 : b4RawGapContribution ![0, 4, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 5, 5] = b4GapPatternWeight 4 5 5 * 0 :=
      b4GapContribution_from_row 0 4 5 5 0 row_00_04_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_05

theorem row_00_04_05_06 : b4RowContribution (![0, 4, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 9, 15] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 9 + 15 = 28
    decide
  have hzsq : (∑ i, (((![0, 4, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 322 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 9^2 + 15^2 = 322
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_05_06

theorem weighted_00_04_05_06 : b4RawGapContribution ![0, 4, 5, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 5, 6] = b4GapPatternWeight 4 5 6 * 0 :=
      b4GapContribution_from_row 0 4 5 6 0 row_00_04_05_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_06

theorem row_00_04_05_07 : b4RowContribution (![0, 4, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 9, 16] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 9 + 16 = 29
    decide
  have hzsq : (∑ i, (((![0, 4, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 353 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 9^2 + 16^2 = 353
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_05_07

theorem weighted_00_04_05_07 : b4RawGapContribution ![0, 4, 5, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 5, 7] = b4GapPatternWeight 4 5 7 * 0 :=
      b4GapContribution_from_row 0 4 5 7 0 row_00_04_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_07

theorem row_00_04_05_08 : b4RowContribution (![0, 4, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 9, 17] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 9 + 17 = 30
    decide
  have hzsq : (∑ i, (((![0, 4, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 386 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 9^2 + 17^2 = 386
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_05_08

theorem weighted_00_04_05_08 : b4RawGapContribution ![0, 4, 5, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 5, 8] = b4GapPatternWeight 4 5 8 * 0 :=
      b4GapContribution_from_row 0 4 5 8 0 row_00_04_05_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_08

theorem row_00_04_05_09 : b4RowContribution (![0, 4, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 9, 18] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 9 + 18 = 31
    decide
  have hzsq : (∑ i, (((![0, 4, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 421 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 9^2 + 18^2 = 421
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_05_09

theorem weighted_00_04_05_09 : b4RawGapContribution ![0, 4, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 5, 9] = b4GapPatternWeight 4 5 9 * 0 :=
      b4GapContribution_from_row 0 4 5 9 0 row_00_04_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_09

theorem row_00_04_05_10 : b4RowContribution (![0, 4, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 9, 19] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 9 + 19 = 32
    decide
  have hzsq : (∑ i, (((![0, 4, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 458 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 9^2 + 19^2 = 458
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_05_10

theorem weighted_00_04_05_10 : b4RawGapContribution ![0, 4, 5, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 5, 10] = b4GapPatternWeight 4 5 10 * 0 :=
      b4GapContribution_from_row 0 4 5 10 0 row_00_04_05_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_10

theorem row_00_04_05_11 : b4RowContribution (![0, 4, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 9, 20] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 9 + 20 = 33
    decide
  have hzsq : (∑ i, (((![0, 4, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 497 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 9^2 + 20^2 = 497
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_05_11

theorem weighted_00_04_05_11 : b4RawGapContribution ![0, 4, 5, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 5, 11] = b4GapPatternWeight 4 5 11 * 0 :=
      b4GapContribution_from_row 0 4 5 11 0 row_00_04_05_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_11

theorem row_00_04_05_12 : b4RowContribution (![0, 4, 9, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 9, 21] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 9 + 21 = 34
    decide
  have hzsq : (∑ i, (((![0, 4, 9, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 538 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 9^2 + 21^2 = 538
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_05_12

theorem weighted_00_04_05_12 : b4RawGapContribution ![0, 4, 5, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 5, 12] = b4GapPatternWeight 4 5 12 * 0 :=
      b4GapContribution_from_row 0 4 5 12 0 row_00_04_05_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_12

theorem row_00_04_05_13 : b4RowContribution (![0, 4, 9, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 9, 22] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 9 + 22 = 35
    decide
  have hzsq : (∑ i, (((![0, 4, 9, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 581 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 9^2 + 22^2 = 581
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_05_13

theorem weighted_00_04_05_13 : b4RawGapContribution ![0, 4, 5, 13] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 5, 13] = b4GapPatternWeight 4 5 13 * 0 :=
      b4GapContribution_from_row 0 4 5 13 0 row_00_04_05_13
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_13

theorem row_00_04_05_14 : b4RowContribution (![0, 4, 9, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 9, 23] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 9 + 23 = 36
    decide
  have hzsq : (∑ i, (((![0, 4, 9, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 626 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 9^2 + 23^2 = 626
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_05_14

theorem weighted_00_04_05_14 : b4RawGapContribution ![0, 4, 5, 14] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 5, 14] = b4GapPatternWeight 4 5 14 * 0 :=
      b4GapContribution_from_row 0 4 5 14 0 row_00_04_05_14
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_14

theorem row_00_04_05_15 : b4RowContribution (![0, 4, 9, 24] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 9, 24] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 9 + 24 = 37
    decide
  have hzsq : (∑ i, (((![0, 4, 9, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 673 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 9^2 + 24^2 = 673
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_05_15

theorem weighted_00_04_05_15 : b4RawGapContribution ![0, 4, 5, 15] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 5, 15] = b4GapPatternWeight 4 5 15 * 0 :=
      b4GapContribution_from_row 0 4 5 15 0 row_00_04_05_15
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_05_15

def dvalues_00_04_05 : Fin 16 → ℕ := ![0, 0, 1128, 360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_04_05

theorem dblock_00_04_05 : b4GapPatternDBlock 0 4 5 = 1488 := by
  calc
    b4GapPatternDBlock 0 4 5 = ∑ d : Fin 16, dvalues_00_04_05 d := by
      apply b4GapDBlock_of_rows 0 4 5 dvalues_00_04_05
      intro d
      fin_cases d
      · exact weighted_00_04_05_00
      · exact weighted_00_04_05_01
      · exact weighted_00_04_05_02
      · exact weighted_00_04_05_03
      · exact weighted_00_04_05_04
      · exact weighted_00_04_05_05
      · exact weighted_00_04_05_06
      · exact weighted_00_04_05_07
      · exact weighted_00_04_05_08
      · exact weighted_00_04_05_09
      · exact weighted_00_04_05_10
      · exact weighted_00_04_05_11
      · exact weighted_00_04_05_12
      · exact weighted_00_04_05_13
      · exact weighted_00_04_05_14
      · exact weighted_00_04_05_15
    _ = 1488 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_04_05

end Paper7MomentGapNumeric
