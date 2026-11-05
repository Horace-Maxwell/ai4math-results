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

theorem row_04_05_00_00 : b4RowContribution (![4, 9, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 9, 9, 9] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 9 + 9 + 9 = 31
    decide
  have hzsq : (∑ i, (((![4, 9, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 259 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 9^2 + 9^2 + 9^2 = 259
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_05_00_00

theorem weighted_04_05_00_00 : b4RawGapContribution ![4, 5, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 5, 0, 0] = b4GapPatternWeight 5 0 0 * 0 :=
      b4GapContribution_from_row 4 5 0 0 0 row_04_05_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_05_00_00

def layers_04_05_00_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 35, 40, 43, 44, 43, 40, 35, 30, 25, 20, 15], ![1, 4, 10, 20, 35, 55, 80, 110, 145, 185, 228, 271, 311, 345, 370, 385, 390, 385, 370]]
#print axioms Paper7MomentGapNumeric.layers_04_05_00_01

theorem cells_04_05_00_01 : QTableValid (![4, 9, 9, 10] : Fin 4 → ℕ) layers_04_05_00_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_05_00_01

theorem valid_04_05_00_01 :
    SparseRowValid (![4, 9, 9, 10] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_04_05_00_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 9, 9, 10] : Fin 4 → ℕ) i) = 32 := by
      rw [Fin.sum_univ_four]
      change 4 + 9 + 9 + 10 = 32
      decide
    have hzsq : (∑ i, (((![4, 9, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 278 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 9^2 + 9^2 + 10^2 = 278
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_05_00_01
#print axioms Paper7MomentGapNumeric.valid_04_05_00_01

def qvalues_04_05_00_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_05_00_01

theorem row_04_05_00_01 : b4RowContribution (![4, 9, 9, 10] : Fin 4 → ℕ) = 55 := by
  calc
    b4RowContribution (![4, 9, 9, 10] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_04_05_00_01) :=
      sparseRow_sound (![4, 9, 9, 10] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_04_05_00_01) valid_04_05_00_01
    _ = 55 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_05_00_01 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 55 := by decide
#print axioms Paper7MomentGapNumeric.row_04_05_00_01

theorem weighted_04_05_00_01 : b4RawGapContribution ![4, 5, 0, 1] = 660 := by
  calc
    b4RawGapContribution ![4, 5, 0, 1] = b4GapPatternWeight 5 0 1 * 55 :=
      b4GapContribution_from_row 4 5 0 1 55 row_04_05_00_01
    _ = 660 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_05_00_01

theorem row_04_05_00_02 : b4RowContribution (![4, 9, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 9, 9, 11] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 9 + 9 + 11 = 33
    decide
  have hzsq : (∑ i, (((![4, 9, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 299 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 9^2 + 9^2 + 11^2 = 299
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_05_00_02

theorem weighted_04_05_00_02 : b4RawGapContribution ![4, 5, 0, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 5, 0, 2] = b4GapPatternWeight 5 0 2 * 0 :=
      b4GapContribution_from_row 4 5 0 2 0 row_04_05_00_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_05_00_02

theorem row_04_05_00_03 : b4RowContribution (![4, 9, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 9, 9, 12] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 9 + 9 + 12 = 34
    decide
  have hzsq : (∑ i, (((![4, 9, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 322 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 9^2 + 9^2 + 12^2 = 322
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_05_00_03

theorem weighted_04_05_00_03 : b4RawGapContribution ![4, 5, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 5, 0, 3] = b4GapPatternWeight 5 0 3 * 0 :=
      b4GapContribution_from_row 4 5 0 3 0 row_04_05_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_05_00_03

theorem row_04_05_00_04 : b4RowContribution (![4, 9, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 9, 9, 13] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 9 + 9 + 13 = 35
    decide
  have hzsq : (∑ i, (((![4, 9, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 347 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 9^2 + 9^2 + 13^2 = 347
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_05_00_04

theorem weighted_04_05_00_04 : b4RawGapContribution ![4, 5, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 5, 0, 4] = b4GapPatternWeight 5 0 4 * 0 :=
      b4GapContribution_from_row 4 5 0 4 0 row_04_05_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_05_00_04

theorem row_04_05_00_05 : b4RowContribution (![4, 9, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 9, 9, 14] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 9 + 9 + 14 = 36
    decide
  have hzsq : (∑ i, (((![4, 9, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 374 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 9^2 + 9^2 + 14^2 = 374
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_05_00_05

theorem weighted_04_05_00_05 : b4RawGapContribution ![4, 5, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 5, 0, 5] = b4GapPatternWeight 5 0 5 * 0 :=
      b4GapContribution_from_row 4 5 0 5 0 row_04_05_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_05_00_05

theorem row_04_05_00_06 : b4RowContribution (![4, 9, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 9, 9, 15] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 9 + 9 + 15 = 37
    decide
  have hzsq : (∑ i, (((![4, 9, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 403 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 9^2 + 9^2 + 15^2 = 403
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_05_00_06

theorem weighted_04_05_00_06 : b4RawGapContribution ![4, 5, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 5, 0, 6] = b4GapPatternWeight 5 0 6 * 0 :=
      b4GapContribution_from_row 4 5 0 6 0 row_04_05_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_05_00_06

def dvalues_04_05_00 : Fin 7 → ℕ := ![0, 660, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_05_00

theorem dblock_04_05_00 : b4GapPatternDBlock 4 5 0 = 660 := by
  calc
    b4GapPatternDBlock 4 5 0 = ∑ d : Fin 7, dvalues_04_05_00 d := by
      apply b4GapDBlock_of_rows 4 5 0 dvalues_04_05_00
      intro d
      fin_cases d
      · exact weighted_04_05_00_00
      · exact weighted_04_05_00_01
      · exact weighted_04_05_00_02
      · exact weighted_04_05_00_03
      · exact weighted_04_05_00_04
      · exact weighted_04_05_00_05
      · exact weighted_04_05_00_06
    _ = 660 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_05_00

end Paper7MomentGapNumeric
