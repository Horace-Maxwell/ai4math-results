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

def layers_01_07_01_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 18, 17, 15, 13, 11, 9, 7, 5, 3, 1], ![1, 4, 9, 16, 25, 36, 49, 64, 81, 99, 115, 127, 135, 139, 139, 135, 127, 115, 99]]
#print axioms Paper7MomentGapNumeric.layers_01_07_01_00

theorem cells_01_07_01_00 : QTableValid (![1, 8, 9, 9] : Fin 4 → ℕ) layers_01_07_01_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_07_01_00

theorem valid_01_07_01_00 :
    SparseRowValid (![1, 8, 9, 9] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_01_07_01_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 8, 9, 9] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 1 + 8 + 9 + 9 = 27
      decide
    have hzsq : (∑ i, (((![1, 8, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 227 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 8^2 + 9^2 + 9^2 = 227
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_07_01_00
#print axioms Paper7MomentGapNumeric.valid_01_07_01_00

def qvalues_01_07_01_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_07_01_00

theorem row_01_07_01_00 : b4RowContribution (![1, 8, 9, 9] : Fin 4 → ℕ) = 81 := by
  calc
    b4RowContribution (![1, 8, 9, 9] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_01_07_01_00) :=
      sparseRow_sound (![1, 8, 9, 9] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_01_07_01_00) valid_01_07_01_00
    _ = 81 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_07_01_00 Q := by
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
        _ = 81 := by decide
#print axioms Paper7MomentGapNumeric.row_01_07_01_00

theorem weighted_01_07_01_00 : b4RawGapContribution ![1, 7, 1, 0] = 972 := by
  calc
    b4RawGapContribution ![1, 7, 1, 0] = b4GapPatternWeight 7 1 0 * 81 :=
      b4GapContribution_from_row 1 7 1 0 81 row_01_07_01_00
    _ = 972 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_01_00

theorem row_01_07_01_01 : b4RowContribution (![1, 8, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 9, 10] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 9 + 10 = 28
    decide
  have hzsq : (∑ i, (((![1, 8, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 246 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 9^2 + 10^2 = 246
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_01_01

theorem weighted_01_07_01_01 : b4RawGapContribution ![1, 7, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 1, 1] = b4GapPatternWeight 7 1 1 * 0 :=
      b4GapContribution_from_row 1 7 1 1 0 row_01_07_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_01_01

theorem row_01_07_01_02 : b4RowContribution (![1, 8, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 9, 11] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 9 + 11 = 29
    decide
  have hzsq : (∑ i, (((![1, 8, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 267 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 9^2 + 11^2 = 267
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_01_02

theorem weighted_01_07_01_02 : b4RawGapContribution ![1, 7, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 1, 2] = b4GapPatternWeight 7 1 2 * 0 :=
      b4GapContribution_from_row 1 7 1 2 0 row_01_07_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_01_02

theorem row_01_07_01_03 : b4RowContribution (![1, 8, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 9, 12] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 9 + 12 = 30
    decide
  have hzsq : (∑ i, (((![1, 8, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 290 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 9^2 + 12^2 = 290
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_01_03

theorem weighted_01_07_01_03 : b4RawGapContribution ![1, 7, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 1, 3] = b4GapPatternWeight 7 1 3 * 0 :=
      b4GapContribution_from_row 1 7 1 3 0 row_01_07_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_01_03

theorem row_01_07_01_04 : b4RowContribution (![1, 8, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 9, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 9 + 13 = 31
    decide
  have hzsq : (∑ i, (((![1, 8, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 315 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 9^2 + 13^2 = 315
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_01_04

theorem weighted_01_07_01_04 : b4RawGapContribution ![1, 7, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 1, 4] = b4GapPatternWeight 7 1 4 * 0 :=
      b4GapContribution_from_row 1 7 1 4 0 row_01_07_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_01_04

theorem row_01_07_01_05 : b4RowContribution (![1, 8, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 9, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 9 + 14 = 32
    decide
  have hzsq : (∑ i, (((![1, 8, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 9^2 + 14^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_01_05

theorem weighted_01_07_01_05 : b4RawGapContribution ![1, 7, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 1, 5] = b4GapPatternWeight 7 1 5 * 0 :=
      b4GapContribution_from_row 1 7 1 5 0 row_01_07_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_01_05

theorem row_01_07_01_06 : b4RowContribution (![1, 8, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 9, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 9 + 15 = 33
    decide
  have hzsq : (∑ i, (((![1, 8, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 371 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 9^2 + 15^2 = 371
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_01_06

theorem weighted_01_07_01_06 : b4RawGapContribution ![1, 7, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 1, 6] = b4GapPatternWeight 7 1 6 * 0 :=
      b4GapContribution_from_row 1 7 1 6 0 row_01_07_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_01_06

theorem row_01_07_01_07 : b4RowContribution (![1, 8, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 9, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 9 + 16 = 34
    decide
  have hzsq : (∑ i, (((![1, 8, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 402 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 9^2 + 16^2 = 402
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_01_07

theorem weighted_01_07_01_07 : b4RawGapContribution ![1, 7, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 1, 7] = b4GapPatternWeight 7 1 7 * 0 :=
      b4GapContribution_from_row 1 7 1 7 0 row_01_07_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_01_07

theorem row_01_07_01_08 : b4RowContribution (![1, 8, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 9, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 9 + 17 = 35
    decide
  have hzsq : (∑ i, (((![1, 8, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 435 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 9^2 + 17^2 = 435
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_01_08

theorem weighted_01_07_01_08 : b4RawGapContribution ![1, 7, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 1, 8] = b4GapPatternWeight 7 1 8 * 0 :=
      b4GapContribution_from_row 1 7 1 8 0 row_01_07_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_01_08

theorem row_01_07_01_09 : b4RowContribution (![1, 8, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 9, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 9 + 18 = 36
    decide
  have hzsq : (∑ i, (((![1, 8, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 470 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 9^2 + 18^2 = 470
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_01_09

theorem weighted_01_07_01_09 : b4RawGapContribution ![1, 7, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 1, 9] = b4GapPatternWeight 7 1 9 * 0 :=
      b4GapContribution_from_row 1 7 1 9 0 row_01_07_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_01_09

theorem row_01_07_01_10 : b4RowContribution (![1, 8, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 9, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 9 + 19 = 37
    decide
  have hzsq : (∑ i, (((![1, 8, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 507 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 9^2 + 19^2 = 507
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_01_10

theorem weighted_01_07_01_10 : b4RawGapContribution ![1, 7, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 1, 10] = b4GapPatternWeight 7 1 10 * 0 :=
      b4GapContribution_from_row 1 7 1 10 0 row_01_07_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_01_10

def dvalues_01_07_01 : Fin 11 → ℕ := ![972, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_07_01

theorem dblock_01_07_01 : b4GapPatternDBlock 1 7 1 = 972 := by
  calc
    b4GapPatternDBlock 1 7 1 = ∑ d : Fin 11, dvalues_01_07_01 d := by
      apply b4GapDBlock_of_rows 1 7 1 dvalues_01_07_01
      intro d
      fin_cases d
      · exact weighted_01_07_01_00
      · exact weighted_01_07_01_01
      · exact weighted_01_07_01_02
      · exact weighted_01_07_01_03
      · exact weighted_01_07_01_04
      · exact weighted_01_07_01_05
      · exact weighted_01_07_01_06
      · exact weighted_01_07_01_07
      · exact weighted_01_07_01_08
      · exact weighted_01_07_01_09
      · exact weighted_01_07_01_10
    _ = 972 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_07_01

end Paper7MomentGapNumeric
