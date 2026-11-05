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

def layers_02_03_06_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 17, 18, 18, 18, 18, 18, 17, 15, 12, 9, 6, 3, 1], ![1, 4, 10, 19, 31, 46, 63, 81, 99, 117, 135, 153, 169, 181, 187, 187, 181, 169, 153]]
#print axioms Paper7MomentGapNumeric.layers_02_03_06_00

theorem cells_02_03_06_00 : QTableValid (![2, 5, 11, 11] : Fin 4 → ℕ) layers_02_03_06_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_03_06_00

theorem valid_02_03_06_00 :
    SparseRowValid (![2, 5, 11, 11] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_02_03_06_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 5, 11, 11] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 2 + 5 + 11 + 11 = 29
      decide
    have hzsq : (∑ i, (((![2, 5, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 271 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 5^2 + 11^2 + 11^2 = 271
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_03_06_00
#print axioms Paper7MomentGapNumeric.valid_02_03_06_00

def qvalues_02_03_06_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_03_06_00

theorem row_02_03_06_00 : b4RowContribution (![2, 5, 11, 11] : Fin 4 → ℕ) = 81 := by
  calc
    b4RowContribution (![2, 5, 11, 11] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_02_03_06_00) :=
      sparseRow_sound (![2, 5, 11, 11] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_02_03_06_00) valid_02_03_06_00
    _ = 81 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_03_06_00 Q := by
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
#print axioms Paper7MomentGapNumeric.row_02_03_06_00

theorem weighted_02_03_06_00 : b4RawGapContribution ![2, 3, 6, 0] = 972 := by
  calc
    b4RawGapContribution ![2, 3, 6, 0] = b4GapPatternWeight 3 6 0 * 81 :=
      b4GapContribution_from_row 2 3 6 0 81 row_02_03_06_00
    _ = 972 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_06_00

theorem row_02_03_06_01 : b4RowContribution (![2, 5, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 11, 12] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 11 + 12 = 30
    decide
  have hzsq : (∑ i, (((![2, 5, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 294 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 11^2 + 12^2 = 294
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_06_01

theorem weighted_02_03_06_01 : b4RawGapContribution ![2, 3, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 6, 1] = b4GapPatternWeight 3 6 1 * 0 :=
      b4GapContribution_from_row 2 3 6 1 0 row_02_03_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_06_01

theorem row_02_03_06_02 : b4RowContribution (![2, 5, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 11, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 11 + 13 = 31
    decide
  have hzsq : (∑ i, (((![2, 5, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 319 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 11^2 + 13^2 = 319
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_06_02

theorem weighted_02_03_06_02 : b4RawGapContribution ![2, 3, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 6, 2] = b4GapPatternWeight 3 6 2 * 0 :=
      b4GapContribution_from_row 2 3 6 2 0 row_02_03_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_06_02

theorem row_02_03_06_03 : b4RowContribution (![2, 5, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 11, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 11 + 14 = 32
    decide
  have hzsq : (∑ i, (((![2, 5, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 346 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 11^2 + 14^2 = 346
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_06_03

theorem weighted_02_03_06_03 : b4RawGapContribution ![2, 3, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 6, 3] = b4GapPatternWeight 3 6 3 * 0 :=
      b4GapContribution_from_row 2 3 6 3 0 row_02_03_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_06_03

theorem row_02_03_06_04 : b4RowContribution (![2, 5, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 11, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 11 + 15 = 33
    decide
  have hzsq : (∑ i, (((![2, 5, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 375 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 11^2 + 15^2 = 375
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_06_04

theorem weighted_02_03_06_04 : b4RawGapContribution ![2, 3, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 6, 4] = b4GapPatternWeight 3 6 4 * 0 :=
      b4GapContribution_from_row 2 3 6 4 0 row_02_03_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_06_04

theorem row_02_03_06_05 : b4RowContribution (![2, 5, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 11, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 11 + 16 = 34
    decide
  have hzsq : (∑ i, (((![2, 5, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 406 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 11^2 + 16^2 = 406
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_06_05

theorem weighted_02_03_06_05 : b4RawGapContribution ![2, 3, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 6, 5] = b4GapPatternWeight 3 6 5 * 0 :=
      b4GapContribution_from_row 2 3 6 5 0 row_02_03_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_06_05

theorem row_02_03_06_06 : b4RowContribution (![2, 5, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 11, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 11 + 17 = 35
    decide
  have hzsq : (∑ i, (((![2, 5, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 439 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 11^2 + 17^2 = 439
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_06_06

theorem weighted_02_03_06_06 : b4RawGapContribution ![2, 3, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 6, 6] = b4GapPatternWeight 3 6 6 * 0 :=
      b4GapContribution_from_row 2 3 6 6 0 row_02_03_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_06_06

theorem row_02_03_06_07 : b4RowContribution (![2, 5, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 11, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 11 + 18 = 36
    decide
  have hzsq : (∑ i, (((![2, 5, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 474 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 11^2 + 18^2 = 474
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_06_07

theorem weighted_02_03_06_07 : b4RawGapContribution ![2, 3, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 6, 7] = b4GapPatternWeight 3 6 7 * 0 :=
      b4GapContribution_from_row 2 3 6 7 0 row_02_03_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_06_07

theorem row_02_03_06_08 : b4RowContribution (![2, 5, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 5, 11, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 5 + 11 + 19 = 37
    decide
  have hzsq : (∑ i, (((![2, 5, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 511 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 5^2 + 11^2 + 19^2 = 511
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_03_06_08

theorem weighted_02_03_06_08 : b4RawGapContribution ![2, 3, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 3, 6, 8] = b4GapPatternWeight 3 6 8 * 0 :=
      b4GapContribution_from_row 2 3 6 8 0 row_02_03_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_03_06_08

def dvalues_02_03_06 : Fin 9 → ℕ := ![972, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_03_06

theorem dblock_02_03_06 : b4GapPatternDBlock 2 3 6 = 972 := by
  calc
    b4GapPatternDBlock 2 3 6 = ∑ d : Fin 9, dvalues_02_03_06 d := by
      apply b4GapDBlock_of_rows 2 3 6 dvalues_02_03_06
      intro d
      fin_cases d
      · exact weighted_02_03_06_00
      · exact weighted_02_03_06_01
      · exact weighted_02_03_06_02
      · exact weighted_02_03_06_03
      · exact weighted_02_03_06_04
      · exact weighted_02_03_06_05
      · exact weighted_02_03_06_06
      · exact weighted_02_03_06_07
      · exact weighted_02_03_06_08
    _ = 972 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_03_06

end Paper7MomentGapNumeric
