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

theorem row_04_04_00_00 : b4RowContribution (![4, 8, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 8, 8] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 8 + 8 = 28
    decide
  have hzsq : (∑ i, (((![4, 8, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 208 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 8^2 + 8^2 = 208
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_00_00

theorem weighted_04_04_00_00 : b4RawGapContribution ![4, 4, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 0, 0] = b4GapPatternWeight 4 0 0 * 0 :=
      b4GapContribution_from_row 4 4 0 0 0 row_04_04_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_00_00

def layers_04_04_00_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 35, 38, 39, 38, 35, 30, 25, 20, 15, 10, 6], ![1, 4, 10, 20, 35, 55, 80, 110, 145, 183, 221, 256, 285, 305, 315, 315, 305, 285, 256]]
#print axioms Paper7MomentGapNumeric.layers_04_04_00_01

theorem cells_04_04_00_01 : QTableValid (![4, 8, 8, 9] : Fin 4 → ℕ) layers_04_04_00_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_04_00_01

theorem valid_04_04_00_01 :
    SparseRowValid (![4, 8, 8, 9] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_04_04_00_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 8, 8, 9] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 4 + 8 + 8 + 9 = 29
      decide
    have hzsq : (∑ i, (((![4, 8, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 225 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 8^2 + 8^2 + 9^2 = 225
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_04_00_01
#print axioms Paper7MomentGapNumeric.valid_04_04_00_01

def qvalues_04_04_00_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_04_00_01

theorem row_04_04_00_01 : b4RowContribution (![4, 8, 8, 9] : Fin 4 → ℕ) = 80 := by
  calc
    b4RowContribution (![4, 8, 8, 9] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_04_04_00_01) :=
      sparseRow_sound (![4, 8, 8, 9] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_04_04_00_01) valid_04_04_00_01
    _ = 80 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_04_00_01 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 80 := by decide
#print axioms Paper7MomentGapNumeric.row_04_04_00_01

theorem weighted_04_04_00_01 : b4RawGapContribution ![4, 4, 0, 1] = 960 := by
  calc
    b4RawGapContribution ![4, 4, 0, 1] = b4GapPatternWeight 4 0 1 * 80 :=
      b4GapContribution_from_row 4 4 0 1 80 row_04_04_00_01
    _ = 960 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_00_01

theorem row_04_04_00_02 : b4RowContribution (![4, 8, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 8, 10] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 8 + 10 = 30
    decide
  have hzsq : (∑ i, (((![4, 8, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 244 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 8^2 + 10^2 = 244
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_00_02

theorem weighted_04_04_00_02 : b4RawGapContribution ![4, 4, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 0, 2] = b4GapPatternWeight 4 0 2 * 0 :=
      b4GapContribution_from_row 4 4 0 2 0 row_04_04_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_00_02

theorem row_04_04_00_03 : b4RowContribution (![4, 8, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 8, 11] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 8 + 11 = 31
    decide
  have hzsq : (∑ i, (((![4, 8, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 265 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 8^2 + 11^2 = 265
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_00_03

theorem weighted_04_04_00_03 : b4RawGapContribution ![4, 4, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 0, 3] = b4GapPatternWeight 4 0 3 * 0 :=
      b4GapContribution_from_row 4 4 0 3 0 row_04_04_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_00_03

theorem row_04_04_00_04 : b4RowContribution (![4, 8, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 8, 12] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 8 + 12 = 32
    decide
  have hzsq : (∑ i, (((![4, 8, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 288 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 8^2 + 12^2 = 288
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_00_04

theorem weighted_04_04_00_04 : b4RawGapContribution ![4, 4, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 0, 4] = b4GapPatternWeight 4 0 4 * 0 :=
      b4GapContribution_from_row 4 4 0 4 0 row_04_04_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_00_04

theorem row_04_04_00_05 : b4RowContribution (![4, 8, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 8, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 8 + 13 = 33
    decide
  have hzsq : (∑ i, (((![4, 8, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 313 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 8^2 + 13^2 = 313
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_00_05

theorem weighted_04_04_00_05 : b4RawGapContribution ![4, 4, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 0, 5] = b4GapPatternWeight 4 0 5 * 0 :=
      b4GapContribution_from_row 4 4 0 5 0 row_04_04_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_00_05

theorem row_04_04_00_06 : b4RowContribution (![4, 8, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 8, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 8 + 14 = 34
    decide
  have hzsq : (∑ i, (((![4, 8, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 340 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 8^2 + 14^2 = 340
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_00_06

theorem weighted_04_04_00_06 : b4RawGapContribution ![4, 4, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 0, 6] = b4GapPatternWeight 4 0 6 * 0 :=
      b4GapContribution_from_row 4 4 0 6 0 row_04_04_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_00_06

theorem row_04_04_00_07 : b4RowContribution (![4, 8, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 8, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 8 + 15 = 35
    decide
  have hzsq : (∑ i, (((![4, 8, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 369 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 8^2 + 15^2 = 369
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_00_07

theorem weighted_04_04_00_07 : b4RawGapContribution ![4, 4, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 0, 7] = b4GapPatternWeight 4 0 7 * 0 :=
      b4GapContribution_from_row 4 4 0 7 0 row_04_04_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_00_07

theorem row_04_04_00_08 : b4RowContribution (![4, 8, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 8, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 8 + 16 = 36
    decide
  have hzsq : (∑ i, (((![4, 8, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 400 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 8^2 + 16^2 = 400
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_00_08

theorem weighted_04_04_00_08 : b4RawGapContribution ![4, 4, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 0, 8] = b4GapPatternWeight 4 0 8 * 0 :=
      b4GapContribution_from_row 4 4 0 8 0 row_04_04_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_00_08

theorem row_04_04_00_09 : b4RowContribution (![4, 8, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 8, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 8 + 17 = 37
    decide
  have hzsq : (∑ i, (((![4, 8, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 433 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 8^2 + 17^2 = 433
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_00_09

theorem weighted_04_04_00_09 : b4RawGapContribution ![4, 4, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 0, 9] = b4GapPatternWeight 4 0 9 * 0 :=
      b4GapContribution_from_row 4 4 0 9 0 row_04_04_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_00_09

def dvalues_04_04_00 : Fin 10 → ℕ := ![0, 960, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_04_00

theorem dblock_04_04_00 : b4GapPatternDBlock 4 4 0 = 960 := by
  calc
    b4GapPatternDBlock 4 4 0 = ∑ d : Fin 10, dvalues_04_04_00 d := by
      apply b4GapDBlock_of_rows 4 4 0 dvalues_04_04_00
      intro d
      fin_cases d
      · exact weighted_04_04_00_00
      · exact weighted_04_04_00_01
      · exact weighted_04_04_00_02
      · exact weighted_04_04_00_03
      · exact weighted_04_04_00_04
      · exact weighted_04_04_00_05
      · exact weighted_04_04_00_06
      · exact weighted_04_04_00_07
      · exact weighted_04_04_00_08
      · exact weighted_04_04_00_09
    _ = 960 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_04_00

end Paper7MomentGapNumeric
