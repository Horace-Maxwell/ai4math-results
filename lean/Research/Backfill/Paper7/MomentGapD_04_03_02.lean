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

def layers_04_03_02_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 34, 37, 38, 37, 34, 30, 25, 20, 15, 10, 6], ![1, 4, 10, 20, 35, 55, 80, 110, 144, 181, 218, 252, 280, 300, 310, 310, 300, 280, 252]]
#print axioms Paper7MomentGapNumeric.layers_04_03_02_00

theorem cells_04_03_02_00 : QTableValid (![4, 7, 9, 9] : Fin 4 → ℕ) layers_04_03_02_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_03_02_00

theorem valid_04_03_02_00 :
    SparseRowValid (![4, 7, 9, 9] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_04_03_02_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 7, 9, 9] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 4 + 7 + 9 + 9 = 29
      decide
    have hzsq : (∑ i, (((![4, 7, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 227 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 7^2 + 9^2 + 9^2 = 227
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_03_02_00
#print axioms Paper7MomentGapNumeric.valid_04_03_02_00

def qvalues_04_03_02_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_03_02_00

theorem row_04_03_02_00 : b4RowContribution (![4, 7, 9, 9] : Fin 4 → ℕ) = 55 := by
  calc
    b4RowContribution (![4, 7, 9, 9] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_04_03_02_00) :=
      sparseRow_sound (![4, 7, 9, 9] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_04_03_02_00) valid_04_03_02_00
    _ = 55 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_03_02_00 Q := by
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
#print axioms Paper7MomentGapNumeric.row_04_03_02_00

theorem weighted_04_03_02_00 : b4RawGapContribution ![4, 3, 2, 0] = 660 := by
  calc
    b4RawGapContribution ![4, 3, 2, 0] = b4GapPatternWeight 3 2 0 * 55 :=
      b4GapContribution_from_row 4 3 2 0 55 row_04_03_02_00
    _ = 660 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_02_00

theorem row_04_03_02_01 : b4RowContribution (![4, 7, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 9, 10] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 9 + 10 = 30
    decide
  have hzsq : (∑ i, (((![4, 7, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 246 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 9^2 + 10^2 = 246
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_02_01

theorem weighted_04_03_02_01 : b4RawGapContribution ![4, 3, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 2, 1] = b4GapPatternWeight 3 2 1 * 0 :=
      b4GapContribution_from_row 4 3 2 1 0 row_04_03_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_02_01

theorem row_04_03_02_02 : b4RowContribution (![4, 7, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 9, 11] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 9 + 11 = 31
    decide
  have hzsq : (∑ i, (((![4, 7, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 267 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 9^2 + 11^2 = 267
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_02_02

theorem weighted_04_03_02_02 : b4RawGapContribution ![4, 3, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 2, 2] = b4GapPatternWeight 3 2 2 * 0 :=
      b4GapContribution_from_row 4 3 2 2 0 row_04_03_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_02_02

theorem row_04_03_02_03 : b4RowContribution (![4, 7, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 9, 12] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 9 + 12 = 32
    decide
  have hzsq : (∑ i, (((![4, 7, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 290 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 9^2 + 12^2 = 290
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_02_03

theorem weighted_04_03_02_03 : b4RawGapContribution ![4, 3, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 2, 3] = b4GapPatternWeight 3 2 3 * 0 :=
      b4GapContribution_from_row 4 3 2 3 0 row_04_03_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_02_03

theorem row_04_03_02_04 : b4RowContribution (![4, 7, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 9, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 9 + 13 = 33
    decide
  have hzsq : (∑ i, (((![4, 7, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 315 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 9^2 + 13^2 = 315
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_02_04

theorem weighted_04_03_02_04 : b4RawGapContribution ![4, 3, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 2, 4] = b4GapPatternWeight 3 2 4 * 0 :=
      b4GapContribution_from_row 4 3 2 4 0 row_04_03_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_02_04

theorem row_04_03_02_05 : b4RowContribution (![4, 7, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 9, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 9 + 14 = 34
    decide
  have hzsq : (∑ i, (((![4, 7, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 9^2 + 14^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_02_05

theorem weighted_04_03_02_05 : b4RawGapContribution ![4, 3, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 2, 5] = b4GapPatternWeight 3 2 5 * 0 :=
      b4GapContribution_from_row 4 3 2 5 0 row_04_03_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_02_05

theorem row_04_03_02_06 : b4RowContribution (![4, 7, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 9, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 9 + 15 = 35
    decide
  have hzsq : (∑ i, (((![4, 7, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 371 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 9^2 + 15^2 = 371
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_02_06

theorem weighted_04_03_02_06 : b4RawGapContribution ![4, 3, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 2, 6] = b4GapPatternWeight 3 2 6 * 0 :=
      b4GapContribution_from_row 4 3 2 6 0 row_04_03_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_02_06

theorem row_04_03_02_07 : b4RowContribution (![4, 7, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 9, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 9 + 16 = 36
    decide
  have hzsq : (∑ i, (((![4, 7, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 402 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 9^2 + 16^2 = 402
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_02_07

theorem weighted_04_03_02_07 : b4RawGapContribution ![4, 3, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 2, 7] = b4GapPatternWeight 3 2 7 * 0 :=
      b4GapContribution_from_row 4 3 2 7 0 row_04_03_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_02_07

theorem row_04_03_02_08 : b4RowContribution (![4, 7, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 9, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 9 + 17 = 37
    decide
  have hzsq : (∑ i, (((![4, 7, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 435 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 9^2 + 17^2 = 435
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_02_08

theorem weighted_04_03_02_08 : b4RawGapContribution ![4, 3, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 2, 8] = b4GapPatternWeight 3 2 8 * 0 :=
      b4GapContribution_from_row 4 3 2 8 0 row_04_03_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_02_08

def dvalues_04_03_02 : Fin 9 → ℕ := ![660, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_03_02

theorem dblock_04_03_02 : b4GapPatternDBlock 4 3 2 = 660 := by
  calc
    b4GapPatternDBlock 4 3 2 = ∑ d : Fin 9, dvalues_04_03_02 d := by
      apply b4GapDBlock_of_rows 4 3 2 dvalues_04_03_02
      intro d
      fin_cases d
      · exact weighted_04_03_02_00
      · exact weighted_04_03_02_01
      · exact weighted_04_03_02_02
      · exact weighted_04_03_02_03
      · exact weighted_04_03_02_04
      · exact weighted_04_03_02_05
      · exact weighted_04_03_02_06
      · exact weighted_04_03_02_07
      · exact weighted_04_03_02_08
    _ = 660 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_03_02

end Paper7MomentGapNumeric
