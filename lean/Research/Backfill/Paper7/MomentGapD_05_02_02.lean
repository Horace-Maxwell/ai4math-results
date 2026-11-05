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

theorem row_05_02_02_00 : b4RowContribution (![5, 7, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 9, 9] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 9 + 9 = 30
    decide
  have hzsq : (∑ i, (((![5, 7, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 236 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 9^2 + 9^2 = 236
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_02_00

theorem weighted_05_02_02_00 : b4RawGapContribution ![5, 2, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 2, 0] = b4GapPatternWeight 2 2 0 * 0 :=
      b4GapContribution_from_row 5 2 2 0 0 row_05_02_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_02_00

theorem row_05_02_02_01 : b4RowContribution (![5, 7, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 9, 10] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 9 + 10 = 31
    decide
  have hzsq : (∑ i, (((![5, 7, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 255 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 9^2 + 10^2 = 255
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_02_01

theorem weighted_05_02_02_01 : b4RawGapContribution ![5, 2, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 2, 1] = b4GapPatternWeight 2 2 1 * 0 :=
      b4GapContribution_from_row 5 2 2 1 0 row_05_02_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_02_01

def layers_05_02_02_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 27, 33, 38, 42, 44, 44, 42, 38, 33, 27, 21, 15, 10], ![1, 4, 10, 20, 35, 56, 83, 116, 154, 196, 240, 284, 325, 360, 387, 404, 410, 404, 387]]
#print axioms Paper7MomentGapNumeric.layers_05_02_02_02

theorem cells_05_02_02_02 : QTableValid (![5, 7, 9, 11] : Fin 4 → ℕ) layers_05_02_02_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_05_02_02_02

theorem valid_05_02_02_02 :
    SparseRowValid (![5, 7, 9, 11] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_05_02_02_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![5, 7, 9, 11] : Fin 4 → ℕ) i) = 32 := by
      rw [Fin.sum_univ_four]
      change 5 + 7 + 9 + 11 = 32
      decide
    have hzsq : (∑ i, (((![5, 7, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 276 := by
      rw [Fin.sum_univ_four]
      change (5 : ℤ)^2 + 7^2 + 9^2 + 11^2 = 276
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_05_02_02_02
#print axioms Paper7MomentGapNumeric.valid_05_02_02_02

def qvalues_05_02_02_02 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_05_02_02_02

theorem row_05_02_02_02 : b4RowContribution (![5, 7, 9, 11] : Fin 4 → ℕ) = 1 := by
  calc
    b4RowContribution (![5, 7, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({0} : Finset (Fin 19)) (fun _ => layers_05_02_02_02) :=
      sparseRow_sound (![5, 7, 9, 11] : Fin 4 → ℕ) ({0} : Finset (Fin 19)) (fun _ => layers_05_02_02_02) valid_05_02_02_02
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_05_02_02_02 Q := by
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
#print axioms Paper7MomentGapNumeric.row_05_02_02_02

theorem weighted_05_02_02_02 : b4RawGapContribution ![5, 2, 2, 2] = 24 := by
  calc
    b4RawGapContribution ![5, 2, 2, 2] = b4GapPatternWeight 2 2 2 * 1 :=
      b4GapContribution_from_row 5 2 2 2 1 row_05_02_02_02
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_02_02

theorem row_05_02_02_03 : b4RowContribution (![5, 7, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 9, 12] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 9 + 12 = 33
    decide
  have hzsq : (∑ i, (((![5, 7, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 299 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 9^2 + 12^2 = 299
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_02_03

theorem weighted_05_02_02_03 : b4RawGapContribution ![5, 2, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 2, 3] = b4GapPatternWeight 2 2 3 * 0 :=
      b4GapContribution_from_row 5 2 2 3 0 row_05_02_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_02_03

theorem row_05_02_02_04 : b4RowContribution (![5, 7, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 9, 13] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 9 + 13 = 34
    decide
  have hzsq : (∑ i, (((![5, 7, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 324 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 9^2 + 13^2 = 324
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_02_04

theorem weighted_05_02_02_04 : b4RawGapContribution ![5, 2, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 2, 4] = b4GapPatternWeight 2 2 4 * 0 :=
      b4GapContribution_from_row 5 2 2 4 0 row_05_02_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_02_04

theorem row_05_02_02_05 : b4RowContribution (![5, 7, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 9, 14] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 9 + 14 = 35
    decide
  have hzsq : (∑ i, (((![5, 7, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 351 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 9^2 + 14^2 = 351
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_02_05

theorem weighted_05_02_02_05 : b4RawGapContribution ![5, 2, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 2, 5] = b4GapPatternWeight 2 2 5 * 0 :=
      b4GapContribution_from_row 5 2 2 5 0 row_05_02_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_02_05

theorem row_05_02_02_06 : b4RowContribution (![5, 7, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 9, 15] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 9 + 15 = 36
    decide
  have hzsq : (∑ i, (((![5, 7, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 380 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 9^2 + 15^2 = 380
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_02_06

theorem weighted_05_02_02_06 : b4RawGapContribution ![5, 2, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 2, 6] = b4GapPatternWeight 2 2 6 * 0 :=
      b4GapContribution_from_row 5 2 2 6 0 row_05_02_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_02_06

theorem row_05_02_02_07 : b4RowContribution (![5, 7, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 9, 16] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 9 + 16 = 37
    decide
  have hzsq : (∑ i, (((![5, 7, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 411 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 9^2 + 16^2 = 411
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_02_07

theorem weighted_05_02_02_07 : b4RawGapContribution ![5, 2, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 2, 7] = b4GapPatternWeight 2 2 7 * 0 :=
      b4GapContribution_from_row 5 2 2 7 0 row_05_02_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_02_07

def dvalues_05_02_02 : Fin 8 → ℕ := ![0, 0, 24, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_02_02

theorem dblock_05_02_02 : b4GapPatternDBlock 5 2 2 = 24 := by
  calc
    b4GapPatternDBlock 5 2 2 = ∑ d : Fin 8, dvalues_05_02_02 d := by
      apply b4GapDBlock_of_rows 5 2 2 dvalues_05_02_02
      intro d
      fin_cases d
      · exact weighted_05_02_02_00
      · exact weighted_05_02_02_01
      · exact weighted_05_02_02_02
      · exact weighted_05_02_02_03
      · exact weighted_05_02_02_04
      · exact weighted_05_02_02_05
      · exact weighted_05_02_02_06
      · exact weighted_05_02_02_07
    _ = 24 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_02_02

end Paper7MomentGapNumeric
