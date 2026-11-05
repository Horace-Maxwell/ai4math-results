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

def layers_03_02_06_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 21, 23, 24, 24, 24, 24, 23, 21, 18, 14, 10, 6, 3], ![1, 4, 10, 20, 34, 52, 73, 96, 120, 144, 168, 192, 214, 232, 244, 248, 244, 232, 214]]
#print axioms Paper7MomentGapNumeric.layers_03_02_06_00

theorem cells_03_02_06_00 : QTableValid (![3, 5, 11, 11] : Fin 4 → ℕ) layers_03_02_06_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_02_06_00

theorem valid_03_02_06_00 :
    SparseRowValid (![3, 5, 11, 11] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_03_02_06_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 5, 11, 11] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 3 + 5 + 11 + 11 = 30
      decide
    have hzsq : (∑ i, (((![3, 5, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 276 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 5^2 + 11^2 + 11^2 = 276
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_02_06_00
#print axioms Paper7MomentGapNumeric.valid_03_02_06_00

def qvalues_03_02_06_00 : Fin 19 → ℕ := ![0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_02_06_00

theorem row_03_02_06_00 : b4RowContribution (![3, 5, 11, 11] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![3, 5, 11, 11] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_03_02_06_00) :=
      sparseRow_sound (![3, 5, 11, 11] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_03_02_06_00) valid_03_02_06_00
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_02_06_00 Q := by
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
#print axioms Paper7MomentGapNumeric.row_03_02_06_00

theorem weighted_03_02_06_00 : b4RawGapContribution ![3, 2, 6, 0] = 240 := by
  calc
    b4RawGapContribution ![3, 2, 6, 0] = b4GapPatternWeight 2 6 0 * 20 :=
      b4GapContribution_from_row 3 2 6 0 20 row_03_02_06_00
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_06_00

theorem row_03_02_06_01 : b4RowContribution (![3, 5, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 11, 12] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 11 + 12 = 31
    decide
  have hzsq : (∑ i, (((![3, 5, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 299 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 11^2 + 12^2 = 299
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_06_01

theorem weighted_03_02_06_01 : b4RawGapContribution ![3, 2, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 6, 1] = b4GapPatternWeight 2 6 1 * 0 :=
      b4GapContribution_from_row 3 2 6 1 0 row_03_02_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_06_01

theorem row_03_02_06_02 : b4RowContribution (![3, 5, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 11, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 11 + 13 = 32
    decide
  have hzsq : (∑ i, (((![3, 5, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 324 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 11^2 + 13^2 = 324
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_06_02

theorem weighted_03_02_06_02 : b4RawGapContribution ![3, 2, 6, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 6, 2] = b4GapPatternWeight 2 6 2 * 0 :=
      b4GapContribution_from_row 3 2 6 2 0 row_03_02_06_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_06_02

theorem row_03_02_06_03 : b4RowContribution (![3, 5, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 11, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 11 + 14 = 33
    decide
  have hzsq : (∑ i, (((![3, 5, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 351 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 11^2 + 14^2 = 351
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_06_03

theorem weighted_03_02_06_03 : b4RawGapContribution ![3, 2, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 6, 3] = b4GapPatternWeight 2 6 3 * 0 :=
      b4GapContribution_from_row 3 2 6 3 0 row_03_02_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_06_03

theorem row_03_02_06_04 : b4RowContribution (![3, 5, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 11, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 11 + 15 = 34
    decide
  have hzsq : (∑ i, (((![3, 5, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 380 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 11^2 + 15^2 = 380
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_06_04

theorem weighted_03_02_06_04 : b4RawGapContribution ![3, 2, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 6, 4] = b4GapPatternWeight 2 6 4 * 0 :=
      b4GapContribution_from_row 3 2 6 4 0 row_03_02_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_06_04

theorem row_03_02_06_05 : b4RowContribution (![3, 5, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 11, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 11 + 16 = 35
    decide
  have hzsq : (∑ i, (((![3, 5, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 411 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 11^2 + 16^2 = 411
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_06_05

theorem weighted_03_02_06_05 : b4RawGapContribution ![3, 2, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 6, 5] = b4GapPatternWeight 2 6 5 * 0 :=
      b4GapContribution_from_row 3 2 6 5 0 row_03_02_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_06_05

theorem row_03_02_06_06 : b4RowContribution (![3, 5, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 11, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 11 + 17 = 36
    decide
  have hzsq : (∑ i, (((![3, 5, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 444 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 11^2 + 17^2 = 444
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_06_06

theorem weighted_03_02_06_06 : b4RawGapContribution ![3, 2, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 6, 6] = b4GapPatternWeight 2 6 6 * 0 :=
      b4GapContribution_from_row 3 2 6 6 0 row_03_02_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_06_06

theorem row_03_02_06_07 : b4RowContribution (![3, 5, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 5, 11, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 5 + 11 + 18 = 37
    decide
  have hzsq : (∑ i, (((![3, 5, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 479 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 5^2 + 11^2 + 18^2 = 479
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_02_06_07

theorem weighted_03_02_06_07 : b4RawGapContribution ![3, 2, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 2, 6, 7] = b4GapPatternWeight 2 6 7 * 0 :=
      b4GapContribution_from_row 3 2 6 7 0 row_03_02_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_02_06_07

def dvalues_03_02_06 : Fin 8 → ℕ := ![240, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_02_06

theorem dblock_03_02_06 : b4GapPatternDBlock 3 2 6 = 240 := by
  calc
    b4GapPatternDBlock 3 2 6 = ∑ d : Fin 8, dvalues_03_02_06 d := by
      apply b4GapDBlock_of_rows 3 2 6 dvalues_03_02_06
      intro d
      fin_cases d
      · exact weighted_03_02_06_00
      · exact weighted_03_02_06_01
      · exact weighted_03_02_06_02
      · exact weighted_03_02_06_03
      · exact weighted_03_02_06_04
      · exact weighted_03_02_06_05
      · exact weighted_03_02_06_06
      · exact weighted_03_02_06_07
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_02_06

end Paper7MomentGapNumeric
