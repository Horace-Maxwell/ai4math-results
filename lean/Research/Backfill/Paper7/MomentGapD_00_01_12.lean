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

theorem row_00_01_12_00 : b4RowContribution (![0, 1, 13, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 13, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 13 + 13 = 27
    decide
  have hzsq : (∑ i, (((![0, 1, 13, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 339 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 13^2 + 13^2 = 339
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_12_00

theorem weighted_00_01_12_00 : b4RawGapContribution ![0, 1, 12, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 12, 0] = b4GapPatternWeight 1 12 0 * 0 :=
      b4GapContribution_from_row 0 1 12 0 0 row_00_01_12_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_12_00

theorem row_00_01_12_01 : b4RowContribution (![0, 1, 13, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 13, 14] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 13 + 14 = 28
    decide
  have hzsq : (∑ i, (((![0, 1, 13, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 366 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 13^2 + 14^2 = 366
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_12_01

theorem weighted_00_01_12_01 : b4RawGapContribution ![0, 1, 12, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 12, 1] = b4GapPatternWeight 1 12 1 * 0 :=
      b4GapContribution_from_row 0 1 12 1 0 row_00_01_12_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_12_01

theorem row_00_01_12_02 : b4RowContribution (![0, 1, 13, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 13, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 13 + 15 = 29
    decide
  have hzsq : (∑ i, (((![0, 1, 13, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 395 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 13^2 + 15^2 = 395
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_12_02

theorem weighted_00_01_12_02 : b4RawGapContribution ![0, 1, 12, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 12, 2] = b4GapPatternWeight 1 12 2 * 0 :=
      b4GapContribution_from_row 0 1 12 2 0 row_00_01_12_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_12_02

theorem row_00_01_12_03 : b4RowContribution (![0, 1, 13, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 13, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 13 + 16 = 30
    decide
  have hzsq : (∑ i, (((![0, 1, 13, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 426 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 13^2 + 16^2 = 426
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_12_03

theorem weighted_00_01_12_03 : b4RawGapContribution ![0, 1, 12, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 12, 3] = b4GapPatternWeight 1 12 3 * 0 :=
      b4GapContribution_from_row 0 1 12 3 0 row_00_01_12_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_12_03

theorem row_00_01_12_04 : b4RowContribution (![0, 1, 13, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 13, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 13 + 17 = 31
    decide
  have hzsq : (∑ i, (((![0, 1, 13, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 459 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 13^2 + 17^2 = 459
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_12_04

theorem weighted_00_01_12_04 : b4RawGapContribution ![0, 1, 12, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 12, 4] = b4GapPatternWeight 1 12 4 * 0 :=
      b4GapContribution_from_row 0 1 12 4 0 row_00_01_12_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_12_04

theorem row_00_01_12_05 : b4RowContribution (![0, 1, 13, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 13, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 13 + 18 = 32
    decide
  have hzsq : (∑ i, (((![0, 1, 13, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 494 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 13^2 + 18^2 = 494
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_12_05

theorem weighted_00_01_12_05 : b4RawGapContribution ![0, 1, 12, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 12, 5] = b4GapPatternWeight 1 12 5 * 0 :=
      b4GapContribution_from_row 0 1 12 5 0 row_00_01_12_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_12_05

theorem row_00_01_12_06 : b4RowContribution (![0, 1, 13, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 13, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 13 + 19 = 33
    decide
  have hzsq : (∑ i, (((![0, 1, 13, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 531 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 13^2 + 19^2 = 531
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_12_06

theorem weighted_00_01_12_06 : b4RawGapContribution ![0, 1, 12, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 12, 6] = b4GapPatternWeight 1 12 6 * 0 :=
      b4GapContribution_from_row 0 1 12 6 0 row_00_01_12_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_12_06

def layers_00_01_12_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 28, 28, 28, 28, 28]]
#print axioms Paper7MomentGapNumeric.layers_00_01_12_07

theorem cells_00_01_12_07 : QTableValid (![0, 1, 13, 20] : Fin 4 → ℕ) layers_00_01_12_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_01_12_07

theorem valid_00_01_12_07 :
    SparseRowValid (![0, 1, 13, 20] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_00_01_12_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 1, 13, 20] : Fin 4 → ℕ) i) = 34 := by
      rw [Fin.sum_univ_four]
      change 0 + 1 + 13 + 20 = 34
      decide
    have hzsq : (∑ i, (((![0, 1, 13, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 570 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 1^2 + 13^2 + 20^2 = 570
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_01_12_07
#print axioms Paper7MomentGapNumeric.valid_00_01_12_07

def qvalues_00_01_12_07 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_01_12_07

theorem row_00_01_12_07 : b4RowContribution (![0, 1, 13, 20] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![0, 1, 13, 20] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_00_01_12_07) :=
      sparseRow_sound (![0, 1, 13, 20] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_00_01_12_07) valid_00_01_12_07
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_01_12_07 Q := by
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
#print axioms Paper7MomentGapNumeric.row_00_01_12_07

theorem weighted_00_01_12_07 : b4RawGapContribution ![0, 1, 12, 7] = 24 := by
  calc
    b4RawGapContribution ![0, 1, 12, 7] = b4GapPatternWeight 1 12 7 * 1 :=
      b4GapContribution_from_row 0 1 12 7 1 row_00_01_12_07
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_12_07

theorem row_00_01_12_08 : b4RowContribution (![0, 1, 13, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 13, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 13 + 21 = 35
    decide
  have hzsq : (∑ i, (((![0, 1, 13, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 611 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 13^2 + 21^2 = 611
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_12_08

theorem weighted_00_01_12_08 : b4RawGapContribution ![0, 1, 12, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 12, 8] = b4GapPatternWeight 1 12 8 * 0 :=
      b4GapContribution_from_row 0 1 12 8 0 row_00_01_12_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_12_08

theorem row_00_01_12_09 : b4RowContribution (![0, 1, 13, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 13, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 13 + 22 = 36
    decide
  have hzsq : (∑ i, (((![0, 1, 13, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 654 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 13^2 + 22^2 = 654
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_12_09

theorem weighted_00_01_12_09 : b4RawGapContribution ![0, 1, 12, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 12, 9] = b4GapPatternWeight 1 12 9 * 0 :=
      b4GapContribution_from_row 0 1 12 9 0 row_00_01_12_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_12_09

theorem row_00_01_12_10 : b4RowContribution (![0, 1, 13, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 1, 13, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 1 + 13 + 23 = 37
    decide
  have hzsq : (∑ i, (((![0, 1, 13, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 699 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 1^2 + 13^2 + 23^2 = 699
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_01_12_10

theorem weighted_00_01_12_10 : b4RawGapContribution ![0, 1, 12, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 1, 12, 10] = b4GapPatternWeight 1 12 10 * 0 :=
      b4GapContribution_from_row 0 1 12 10 0 row_00_01_12_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_01_12_10

def dvalues_00_01_12 : Fin 11 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_01_12

theorem dblock_00_01_12 : b4GapPatternDBlock 0 1 12 = 24 := by
  calc
    b4GapPatternDBlock 0 1 12 = ∑ d : Fin 11, dvalues_00_01_12 d := by
      apply b4GapDBlock_of_rows 0 1 12 dvalues_00_01_12
      intro d
      fin_cases d
      · exact weighted_00_01_12_00
      · exact weighted_00_01_12_01
      · exact weighted_00_01_12_02
      · exact weighted_00_01_12_03
      · exact weighted_00_01_12_04
      · exact weighted_00_01_12_05
      · exact weighted_00_01_12_06
      · exact weighted_00_01_12_07
      · exact weighted_00_01_12_08
      · exact weighted_00_01_12_09
      · exact weighted_00_01_12_10
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_01_12

end Paper7MomentGapNumeric
