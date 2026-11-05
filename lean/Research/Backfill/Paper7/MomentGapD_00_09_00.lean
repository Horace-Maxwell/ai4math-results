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

theorem row_00_09_00_00 : b4RowContribution (![0, 9, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 9, 9] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 9 + 9 = 27
    decide
  have hzsq : (∑ i, (((![0, 9, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 243 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 9^2 + 9^2 = 243
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_00_00

theorem weighted_00_09_00_00 : b4RawGapContribution ![0, 9, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 0, 0] = b4GapPatternWeight 9 0 0 * 0 :=
      b4GapContribution_from_row 0 9 0 0 0 row_00_09_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_00_00

theorem row_00_09_00_01 : b4RowContribution (![0, 9, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 9, 10] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 9 + 10 = 28
    decide
  have hzsq : (∑ i, (((![0, 9, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 262 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 9^2 + 10^2 = 262
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_00_01

theorem weighted_00_09_00_01 : b4RawGapContribution ![0, 9, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 0, 1] = b4GapPatternWeight 9 0 1 * 0 :=
      b4GapContribution_from_row 0 9 0 1 0 row_00_09_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_00_01

def layers_00_09_00_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1], ![1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 64, 72, 78, 82, 84, 84, 82, 78, 72]]
#print axioms Paper7MomentGapNumeric.layers_00_09_00_02

theorem cells_00_09_00_02 : QTableValid (![0, 9, 9, 11] : Fin 4 → ℕ) layers_00_09_00_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_09_00_02

theorem valid_00_09_00_02 :
    SparseRowValid (![0, 9, 9, 11] : Fin 4 → ℕ) ({1, 7} : Finset (Fin 19)) (fun _ => layers_00_09_00_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 9, 9, 11] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 0 + 9 + 9 + 11 = 29
      decide
    have hzsq : (∑ i, (((![0, 9, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 283 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 9^2 + 9^2 + 11^2 = 283
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_09_00_02
#print axioms Paper7MomentGapNumeric.valid_00_09_00_02

def qvalues_00_09_00_02 : Fin 19 → ℕ := ![0, 3, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_09_00_02

theorem row_00_09_00_02 : b4RowContribution (![0, 9, 9, 11] : Fin 4 → ℕ) = 39 := by
  calc
    b4RowContribution (![0, 9, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({1, 7} : Finset (Fin 19)) (fun _ => layers_00_09_00_02) :=
      sparseRow_sound (![0, 9, 9, 11] : Fin 4 → ℕ) ({1, 7} : Finset (Fin 19)) (fun _ => layers_00_09_00_02) valid_00_09_00_02
    _ = 39 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_09_00_02 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 39 := by decide
#print axioms Paper7MomentGapNumeric.row_00_09_00_02

theorem weighted_00_09_00_02 : b4RawGapContribution ![0, 9, 0, 2] = 468 := by
  calc
    b4RawGapContribution ![0, 9, 0, 2] = b4GapPatternWeight 9 0 2 * 39 :=
      b4GapContribution_from_row 0 9 0 2 39 row_00_09_00_02
    _ = 468 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_00_02

theorem row_00_09_00_03 : b4RowContribution (![0, 9, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 9, 12] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 9 + 12 = 30
    decide
  have hzsq : (∑ i, (((![0, 9, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 9^2 + 12^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_00_03

theorem weighted_00_09_00_03 : b4RawGapContribution ![0, 9, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 0, 3] = b4GapPatternWeight 9 0 3 * 0 :=
      b4GapContribution_from_row 0 9 0 3 0 row_00_09_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_00_03

theorem row_00_09_00_04 : b4RowContribution (![0, 9, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 9, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 9 + 13 = 31
    decide
  have hzsq : (∑ i, (((![0, 9, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 331 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 9^2 + 13^2 = 331
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_00_04

theorem weighted_00_09_00_04 : b4RawGapContribution ![0, 9, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 0, 4] = b4GapPatternWeight 9 0 4 * 0 :=
      b4GapContribution_from_row 0 9 0 4 0 row_00_09_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_00_04

theorem row_00_09_00_05 : b4RowContribution (![0, 9, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 9, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 9 + 14 = 32
    decide
  have hzsq : (∑ i, (((![0, 9, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 358 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 9^2 + 14^2 = 358
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_00_05

theorem weighted_00_09_00_05 : b4RawGapContribution ![0, 9, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 0, 5] = b4GapPatternWeight 9 0 5 * 0 :=
      b4GapContribution_from_row 0 9 0 5 0 row_00_09_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_00_05

theorem row_00_09_00_06 : b4RowContribution (![0, 9, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 9, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 9 + 15 = 33
    decide
  have hzsq : (∑ i, (((![0, 9, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 387 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 9^2 + 15^2 = 387
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_00_06

theorem weighted_00_09_00_06 : b4RawGapContribution ![0, 9, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 0, 6] = b4GapPatternWeight 9 0 6 * 0 :=
      b4GapContribution_from_row 0 9 0 6 0 row_00_09_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_00_06

theorem row_00_09_00_07 : b4RowContribution (![0, 9, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 9, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 9 + 16 = 34
    decide
  have hzsq : (∑ i, (((![0, 9, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 418 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 9^2 + 16^2 = 418
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_00_07

theorem weighted_00_09_00_07 : b4RawGapContribution ![0, 9, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 0, 7] = b4GapPatternWeight 9 0 7 * 0 :=
      b4GapContribution_from_row 0 9 0 7 0 row_00_09_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_00_07

theorem row_00_09_00_08 : b4RowContribution (![0, 9, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 9, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 9 + 17 = 35
    decide
  have hzsq : (∑ i, (((![0, 9, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 451 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 9^2 + 17^2 = 451
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_00_08

theorem weighted_00_09_00_08 : b4RawGapContribution ![0, 9, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 0, 8] = b4GapPatternWeight 9 0 8 * 0 :=
      b4GapContribution_from_row 0 9 0 8 0 row_00_09_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_00_08

theorem row_00_09_00_09 : b4RowContribution (![0, 9, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 9, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 9 + 18 = 36
    decide
  have hzsq : (∑ i, (((![0, 9, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 486 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 9^2 + 18^2 = 486
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_00_09

theorem weighted_00_09_00_09 : b4RawGapContribution ![0, 9, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 0, 9] = b4GapPatternWeight 9 0 9 * 0 :=
      b4GapContribution_from_row 0 9 0 9 0 row_00_09_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_00_09

theorem row_00_09_00_10 : b4RowContribution (![0, 9, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 9, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 9 + 19 = 37
    decide
  have hzsq : (∑ i, (((![0, 9, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 523 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 9^2 + 19^2 = 523
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_00_10

theorem weighted_00_09_00_10 : b4RawGapContribution ![0, 9, 0, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 0, 10] = b4GapPatternWeight 9 0 10 * 0 :=
      b4GapContribution_from_row 0 9 0 10 0 row_00_09_00_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_00_10

def dvalues_00_09_00 : Fin 11 → ℕ := ![0, 0, 468, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_09_00

theorem dblock_00_09_00 : b4GapPatternDBlock 0 9 0 = 468 := by
  calc
    b4GapPatternDBlock 0 9 0 = ∑ d : Fin 11, dvalues_00_09_00 d := by
      apply b4GapDBlock_of_rows 0 9 0 dvalues_00_09_00
      intro d
      fin_cases d
      · exact weighted_00_09_00_00
      · exact weighted_00_09_00_01
      · exact weighted_00_09_00_02
      · exact weighted_00_09_00_03
      · exact weighted_00_09_00_04
      · exact weighted_00_09_00_05
      · exact weighted_00_09_00_06
      · exact weighted_00_09_00_07
      · exact weighted_00_09_00_08
      · exact weighted_00_09_00_09
      · exact weighted_00_09_00_10
    _ = 468 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_09_00

end Paper7MomentGapNumeric
