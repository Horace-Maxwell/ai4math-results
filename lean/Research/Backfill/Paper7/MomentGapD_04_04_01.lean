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

theorem row_04_04_01_00 : b4RowContribution (![4, 8, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 9, 9] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 9 + 9 = 30
    decide
  have hzsq : (∑ i, (((![4, 8, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 242 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 9^2 + 9^2 = 242
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_01_00

theorem weighted_04_04_01_00 : b4RawGapContribution ![4, 4, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 1, 0] = b4GapPatternWeight 4 1 0 * 0 :=
      b4GapContribution_from_row 4 4 1 0 0 row_04_04_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_01_00

theorem row_04_04_01_01 : b4RowContribution (![4, 8, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 9, 10] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 9 + 10 = 31
    decide
  have hzsq : (∑ i, (((![4, 8, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 261 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 9^2 + 10^2 = 261
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_01_01

theorem weighted_04_04_01_01 : b4RawGapContribution ![4, 4, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 1, 1] = b4GapPatternWeight 4 1 1 * 0 :=
      b4GapContribution_from_row 4 4 1 1 0 row_04_04_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_01_01

def layers_04_04_01_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 35, 39, 41, 41, 39, 35, 30, 25, 20, 15, 10], ![1, 4, 10, 20, 35, 55, 80, 110, 145, 184, 225, 266, 304, 336, 360, 375, 380, 375, 360]]
#print axioms Paper7MomentGapNumeric.layers_04_04_01_02

theorem cells_04_04_01_02 : QTableValid (![4, 8, 9, 11] : Fin 4 → ℕ) layers_04_04_01_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_04_01_02

theorem valid_04_04_01_02 :
    SparseRowValid (![4, 8, 9, 11] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_04_04_01_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 8, 9, 11] : Fin 4 → ℕ) i) = 32 := by
      rw [Fin.sum_univ_four]
      change 4 + 8 + 9 + 11 = 32
      decide
    have hzsq : (∑ i, (((![4, 8, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 282 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 8^2 + 9^2 + 11^2 = 282
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_04_01_02
#print axioms Paper7MomentGapNumeric.valid_04_04_01_02

def qvalues_04_04_01_02 : Fin 19 → ℕ := ![0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_04_01_02

theorem row_04_04_01_02 : b4RowContribution (![4, 8, 9, 11] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![4, 8, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_04_04_01_02) :=
      sparseRow_sound (![4, 8, 9, 11] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_04_04_01_02) valid_04_04_01_02
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_04_01_02 Q := by
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
#print axioms Paper7MomentGapNumeric.row_04_04_01_02

theorem weighted_04_04_01_02 : b4RawGapContribution ![4, 4, 1, 2] = 480 := by
  calc
    b4RawGapContribution ![4, 4, 1, 2] = b4GapPatternWeight 4 1 2 * 20 :=
      b4GapContribution_from_row 4 4 1 2 20 row_04_04_01_02
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_01_02

theorem row_04_04_01_03 : b4RowContribution (![4, 8, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 9, 12] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 9 + 12 = 33
    decide
  have hzsq : (∑ i, (((![4, 8, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 305 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 9^2 + 12^2 = 305
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_01_03

theorem weighted_04_04_01_03 : b4RawGapContribution ![4, 4, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 1, 3] = b4GapPatternWeight 4 1 3 * 0 :=
      b4GapContribution_from_row 4 4 1 3 0 row_04_04_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_01_03

theorem row_04_04_01_04 : b4RowContribution (![4, 8, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 9, 13] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 9 + 13 = 34
    decide
  have hzsq : (∑ i, (((![4, 8, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 330 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 9^2 + 13^2 = 330
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_01_04

theorem weighted_04_04_01_04 : b4RawGapContribution ![4, 4, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 1, 4] = b4GapPatternWeight 4 1 4 * 0 :=
      b4GapContribution_from_row 4 4 1 4 0 row_04_04_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_01_04

theorem row_04_04_01_05 : b4RowContribution (![4, 8, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 9, 14] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 9 + 14 = 35
    decide
  have hzsq : (∑ i, (((![4, 8, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 357 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 9^2 + 14^2 = 357
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_01_05

theorem weighted_04_04_01_05 : b4RawGapContribution ![4, 4, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 1, 5] = b4GapPatternWeight 4 1 5 * 0 :=
      b4GapContribution_from_row 4 4 1 5 0 row_04_04_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_01_05

theorem row_04_04_01_06 : b4RowContribution (![4, 8, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 9, 15] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 9 + 15 = 36
    decide
  have hzsq : (∑ i, (((![4, 8, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 386 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 9^2 + 15^2 = 386
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_01_06

theorem weighted_04_04_01_06 : b4RawGapContribution ![4, 4, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 1, 6] = b4GapPatternWeight 4 1 6 * 0 :=
      b4GapContribution_from_row 4 4 1 6 0 row_04_04_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_01_06

theorem row_04_04_01_07 : b4RowContribution (![4, 8, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 9, 16] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 9 + 16 = 37
    decide
  have hzsq : (∑ i, (((![4, 8, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 417 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 9^2 + 16^2 = 417
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_01_07

theorem weighted_04_04_01_07 : b4RawGapContribution ![4, 4, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 1, 7] = b4GapPatternWeight 4 1 7 * 0 :=
      b4GapContribution_from_row 4 4 1 7 0 row_04_04_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_01_07

def dvalues_04_04_01 : Fin 8 → ℕ := ![0, 0, 480, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_04_01

theorem dblock_04_04_01 : b4GapPatternDBlock 4 4 1 = 480 := by
  calc
    b4GapPatternDBlock 4 4 1 = ∑ d : Fin 8, dvalues_04_04_01 d := by
      apply b4GapDBlock_of_rows 4 4 1 dvalues_04_04_01
      intro d
      fin_cases d
      · exact weighted_04_04_01_00
      · exact weighted_04_04_01_01
      · exact weighted_04_04_01_02
      · exact weighted_04_04_01_03
      · exact weighted_04_04_01_04
      · exact weighted_04_04_01_05
      · exact weighted_04_04_01_06
      · exact weighted_04_04_01_07
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_04_01

end Paper7MomentGapNumeric
