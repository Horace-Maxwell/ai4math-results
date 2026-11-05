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

def layers_01_08_01_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 20, 19, 17, 15, 13, 11, 9, 7, 5], ![1, 4, 9, 16, 25, 36, 49, 64, 81, 100, 120, 138, 152, 162, 168, 170, 168, 162, 152]]
#print axioms Paper7MomentGapNumeric.layers_01_08_01_00

theorem cells_01_08_01_00 : QTableValid (![1, 9, 10, 10] : Fin 4 → ℕ) layers_01_08_01_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_08_01_00

theorem valid_01_08_01_00 :
    SparseRowValid (![1, 9, 10, 10] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_08_01_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 9, 10, 10] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 1 + 9 + 10 + 10 = 30
      decide
    have hzsq : (∑ i, (((![1, 9, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 282 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 9^2 + 10^2 + 10^2 = 282
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_08_01_00
#print axioms Paper7MomentGapNumeric.valid_01_08_01_00

def qvalues_01_08_01_00 : Fin 19 → ℕ := ![1, 0, 0, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_08_01_00

theorem row_01_08_01_00 : b4RowContribution (![1, 9, 10, 10] : Fin 4 → ℕ) = 50 := by
  calc
    b4RowContribution (![1, 9, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_08_01_00) :=
      sparseRow_sound (![1, 9, 10, 10] : Fin 4 → ℕ) ({0, 6} : Finset (Fin 19)) (fun _ => layers_01_08_01_00) valid_01_08_01_00
    _ = 50 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_08_01_00 Q := by
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
        _ = 50 := by decide
#print axioms Paper7MomentGapNumeric.row_01_08_01_00

theorem weighted_01_08_01_00 : b4RawGapContribution ![1, 8, 1, 0] = 600 := by
  calc
    b4RawGapContribution ![1, 8, 1, 0] = b4GapPatternWeight 8 1 0 * 50 :=
      b4GapContribution_from_row 1 8 1 0 50 row_01_08_01_00
    _ = 600 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_01_00

theorem row_01_08_01_01 : b4RowContribution (![1, 9, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 10, 11] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 10 + 11 = 31
    decide
  have hzsq : (∑ i, (((![1, 9, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 303 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 10^2 + 11^2 = 303
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_01_01

theorem weighted_01_08_01_01 : b4RawGapContribution ![1, 8, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 1, 1] = b4GapPatternWeight 8 1 1 * 0 :=
      b4GapContribution_from_row 1 8 1 1 0 row_01_08_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_01_01

theorem row_01_08_01_02 : b4RowContribution (![1, 9, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 10, 12] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 10 + 12 = 32
    decide
  have hzsq : (∑ i, (((![1, 9, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 326 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 10^2 + 12^2 = 326
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_01_02

theorem weighted_01_08_01_02 : b4RawGapContribution ![1, 8, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 1, 2] = b4GapPatternWeight 8 1 2 * 0 :=
      b4GapContribution_from_row 1 8 1 2 0 row_01_08_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_01_02

theorem row_01_08_01_03 : b4RowContribution (![1, 9, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 10, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 10 + 13 = 33
    decide
  have hzsq : (∑ i, (((![1, 9, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 351 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 10^2 + 13^2 = 351
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_01_03

theorem weighted_01_08_01_03 : b4RawGapContribution ![1, 8, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 1, 3] = b4GapPatternWeight 8 1 3 * 0 :=
      b4GapContribution_from_row 1 8 1 3 0 row_01_08_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_01_03

theorem row_01_08_01_04 : b4RowContribution (![1, 9, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 10, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 10 + 14 = 34
    decide
  have hzsq : (∑ i, (((![1, 9, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 378 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 10^2 + 14^2 = 378
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_01_04

theorem weighted_01_08_01_04 : b4RawGapContribution ![1, 8, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 1, 4] = b4GapPatternWeight 8 1 4 * 0 :=
      b4GapContribution_from_row 1 8 1 4 0 row_01_08_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_01_04

theorem row_01_08_01_05 : b4RowContribution (![1, 9, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 10, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 10 + 15 = 35
    decide
  have hzsq : (∑ i, (((![1, 9, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 407 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 10^2 + 15^2 = 407
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_01_05

theorem weighted_01_08_01_05 : b4RawGapContribution ![1, 8, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 1, 5] = b4GapPatternWeight 8 1 5 * 0 :=
      b4GapContribution_from_row 1 8 1 5 0 row_01_08_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_01_05

theorem row_01_08_01_06 : b4RowContribution (![1, 9, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 10, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 10 + 16 = 36
    decide
  have hzsq : (∑ i, (((![1, 9, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 438 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 10^2 + 16^2 = 438
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_01_06

theorem weighted_01_08_01_06 : b4RawGapContribution ![1, 8, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 1, 6] = b4GapPatternWeight 8 1 6 * 0 :=
      b4GapContribution_from_row 1 8 1 6 0 row_01_08_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_01_06

theorem row_01_08_01_07 : b4RowContribution (![1, 9, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 10, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 10 + 17 = 37
    decide
  have hzsq : (∑ i, (((![1, 9, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 471 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 10^2 + 17^2 = 471
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_01_07

theorem weighted_01_08_01_07 : b4RawGapContribution ![1, 8, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 1, 7] = b4GapPatternWeight 8 1 7 * 0 :=
      b4GapContribution_from_row 1 8 1 7 0 row_01_08_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_01_07

def dvalues_01_08_01 : Fin 8 → ℕ := ![600, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_08_01

theorem dblock_01_08_01 : b4GapPatternDBlock 1 8 1 = 600 := by
  calc
    b4GapPatternDBlock 1 8 1 = ∑ d : Fin 8, dvalues_01_08_01 d := by
      apply b4GapDBlock_of_rows 1 8 1 dvalues_01_08_01
      intro d
      fin_cases d
      · exact weighted_01_08_01_00
      · exact weighted_01_08_01_01
      · exact weighted_01_08_01_02
      · exact weighted_01_08_01_03
      · exact weighted_01_08_01_04
      · exact weighted_01_08_01_05
      · exact weighted_01_08_01_06
      · exact weighted_01_08_01_07
    _ = 600 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_08_01

end Paper7MomentGapNumeric
