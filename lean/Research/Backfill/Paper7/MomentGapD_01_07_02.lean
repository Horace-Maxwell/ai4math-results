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

theorem row_01_07_02_00 : b4RowContribution (![1, 8, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 10, 10] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 10 + 10 = 29
    decide
  have hzsq : (∑ i, (((![1, 8, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 265 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 10^2 + 10^2 = 265
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_02_00

theorem weighted_01_07_02_00 : b4RawGapContribution ![1, 7, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 2, 0] = b4GapPatternWeight 7 2 0 * 0 :=
      b4GapContribution_from_row 1 7 2 0 0 row_01_07_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_02_00

def layers_01_07_02_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 18, 18, 17, 15, 13, 11, 9, 7, 5, 3], ![1, 4, 9, 16, 25, 36, 49, 64, 81, 99, 117, 134, 148, 158, 164, 166, 164, 158, 148]]
#print axioms Paper7MomentGapNumeric.layers_01_07_02_01

theorem cells_01_07_02_01 : QTableValid (![1, 8, 10, 11] : Fin 4 → ℕ) layers_01_07_02_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_07_02_01

theorem valid_01_07_02_01 :
    SparseRowValid (![1, 8, 10, 11] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_01_07_02_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 8, 10, 11] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 1 + 8 + 10 + 11 = 30
      decide
    have hzsq : (∑ i, (((![1, 8, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 286 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 8^2 + 10^2 + 11^2 = 286
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_07_02_01
#print axioms Paper7MomentGapNumeric.valid_01_07_02_01

def qvalues_01_07_02_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_07_02_01

theorem row_01_07_02_01 : b4RowContribution (![1, 8, 10, 11] : Fin 4 → ℕ) = 25 := by
  calc
    b4RowContribution (![1, 8, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_01_07_02_01) :=
      sparseRow_sound (![1, 8, 10, 11] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_01_07_02_01) valid_01_07_02_01
    _ = 25 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_07_02_01 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 25 := by decide
#print axioms Paper7MomentGapNumeric.row_01_07_02_01

theorem weighted_01_07_02_01 : b4RawGapContribution ![1, 7, 2, 1] = 600 := by
  calc
    b4RawGapContribution ![1, 7, 2, 1] = b4GapPatternWeight 7 2 1 * 25 :=
      b4GapContribution_from_row 1 7 2 1 25 row_01_07_02_01
    _ = 600 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_02_01

theorem row_01_07_02_02 : b4RowContribution (![1, 8, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 10, 12] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 10 + 12 = 31
    decide
  have hzsq : (∑ i, (((![1, 8, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 309 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 10^2 + 12^2 = 309
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_02_02

theorem weighted_01_07_02_02 : b4RawGapContribution ![1, 7, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 2, 2] = b4GapPatternWeight 7 2 2 * 0 :=
      b4GapContribution_from_row 1 7 2 2 0 row_01_07_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_02_02

theorem row_01_07_02_03 : b4RowContribution (![1, 8, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 10, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 10 + 13 = 32
    decide
  have hzsq : (∑ i, (((![1, 8, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 334 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 10^2 + 13^2 = 334
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_02_03

theorem weighted_01_07_02_03 : b4RawGapContribution ![1, 7, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 2, 3] = b4GapPatternWeight 7 2 3 * 0 :=
      b4GapContribution_from_row 1 7 2 3 0 row_01_07_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_02_03

theorem row_01_07_02_04 : b4RowContribution (![1, 8, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 10, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 10 + 14 = 33
    decide
  have hzsq : (∑ i, (((![1, 8, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 361 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 10^2 + 14^2 = 361
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_02_04

theorem weighted_01_07_02_04 : b4RawGapContribution ![1, 7, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 2, 4] = b4GapPatternWeight 7 2 4 * 0 :=
      b4GapContribution_from_row 1 7 2 4 0 row_01_07_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_02_04

theorem row_01_07_02_05 : b4RowContribution (![1, 8, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 10, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 10 + 15 = 34
    decide
  have hzsq : (∑ i, (((![1, 8, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 390 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 10^2 + 15^2 = 390
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_02_05

theorem weighted_01_07_02_05 : b4RawGapContribution ![1, 7, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 2, 5] = b4GapPatternWeight 7 2 5 * 0 :=
      b4GapContribution_from_row 1 7 2 5 0 row_01_07_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_02_05

theorem row_01_07_02_06 : b4RowContribution (![1, 8, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 10, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 10 + 16 = 35
    decide
  have hzsq : (∑ i, (((![1, 8, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 421 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 10^2 + 16^2 = 421
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_02_06

theorem weighted_01_07_02_06 : b4RawGapContribution ![1, 7, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 2, 6] = b4GapPatternWeight 7 2 6 * 0 :=
      b4GapContribution_from_row 1 7 2 6 0 row_01_07_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_02_06

theorem row_01_07_02_07 : b4RowContribution (![1, 8, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 10, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 10 + 17 = 36
    decide
  have hzsq : (∑ i, (((![1, 8, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 454 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 10^2 + 17^2 = 454
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_02_07

theorem weighted_01_07_02_07 : b4RawGapContribution ![1, 7, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 2, 7] = b4GapPatternWeight 7 2 7 * 0 :=
      b4GapContribution_from_row 1 7 2 7 0 row_01_07_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_02_07

theorem row_01_07_02_08 : b4RowContribution (![1, 8, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 8, 10, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 8 + 10 + 18 = 37
    decide
  have hzsq : (∑ i, (((![1, 8, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 489 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 8^2 + 10^2 + 18^2 = 489
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_07_02_08

theorem weighted_01_07_02_08 : b4RawGapContribution ![1, 7, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 7, 2, 8] = b4GapPatternWeight 7 2 8 * 0 :=
      b4GapContribution_from_row 1 7 2 8 0 row_01_07_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_07_02_08

def dvalues_01_07_02 : Fin 9 → ℕ := ![0, 600, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_07_02

theorem dblock_01_07_02 : b4GapPatternDBlock 1 7 2 = 600 := by
  calc
    b4GapPatternDBlock 1 7 2 = ∑ d : Fin 9, dvalues_01_07_02 d := by
      apply b4GapDBlock_of_rows 1 7 2 dvalues_01_07_02
      intro d
      fin_cases d
      · exact weighted_01_07_02_00
      · exact weighted_01_07_02_01
      · exact weighted_01_07_02_02
      · exact weighted_01_07_02_03
      · exact weighted_01_07_02_04
      · exact weighted_01_07_02_05
      · exact weighted_01_07_02_06
      · exact weighted_01_07_02_07
      · exact weighted_01_07_02_08
    _ = 600 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_07_02

end Paper7MomentGapNumeric
