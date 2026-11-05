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

theorem row_04_01_04_00 : b4RowContribution (![4, 5, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 9, 9] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 9 + 9 = 27
    decide
  have hzsq : (∑ i, (((![4, 5, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 203 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 9^2 + 9^2 = 203
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_04_00

theorem weighted_04_01_04_00 : b4RawGapContribution ![4, 1, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 4, 0] = b4GapPatternWeight 1 4 0 * 0 :=
      b4GapContribution_from_row 4 1 4 0 0 row_04_01_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_04_00

def layers_04_01_04_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 24, 27, 29, 30, 29, 27, 24, 20, 15, 10, 6, 3, 1], ![1, 4, 10, 20, 35, 55, 79, 106, 135, 165, 194, 220, 241, 255, 260, 255, 241, 220, 194]]
#print axioms Paper7MomentGapNumeric.layers_04_01_04_01

theorem cells_04_01_04_01 : QTableValid (![4, 5, 9, 10] : Fin 4 → ℕ) layers_04_01_04_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_01_04_01

theorem valid_04_01_04_01 :
    SparseRowValid (![4, 5, 9, 10] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_04_01_04_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 5, 9, 10] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 4 + 5 + 9 + 10 = 28
      decide
    have hzsq : (∑ i, (((![4, 5, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 222 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 5^2 + 9^2 + 10^2 = 222
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_01_04_01
#print axioms Paper7MomentGapNumeric.valid_04_01_04_01

def qvalues_04_01_04_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 165, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_01_04_01

theorem row_04_01_04_01 : b4RowContribution (![4, 5, 9, 10] : Fin 4 → ℕ) = 165 := by
  calc
    b4RowContribution (![4, 5, 9, 10] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_04_01_04_01) :=
      sparseRow_sound (![4, 5, 9, 10] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_04_01_04_01) valid_04_01_04_01
    _ = 165 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_01_04_01 Q := by
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
        _ = 165 := by decide
#print axioms Paper7MomentGapNumeric.row_04_01_04_01

theorem weighted_04_01_04_01 : b4RawGapContribution ![4, 1, 4, 1] = 3960 := by
  calc
    b4RawGapContribution ![4, 1, 4, 1] = b4GapPatternWeight 1 4 1 * 165 :=
      b4GapContribution_from_row 4 1 4 1 165 row_04_01_04_01
    _ = 3960 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_04_01

theorem row_04_01_04_02 : b4RowContribution (![4, 5, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 9, 11] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 9 + 11 = 29
    decide
  have hzsq : (∑ i, (((![4, 5, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 243 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 9^2 + 11^2 = 243
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_04_02

theorem weighted_04_01_04_02 : b4RawGapContribution ![4, 1, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 4, 2] = b4GapPatternWeight 1 4 2 * 0 :=
      b4GapContribution_from_row 4 1 4 2 0 row_04_01_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_04_02

theorem row_04_01_04_03 : b4RowContribution (![4, 5, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 9, 12] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 9 + 12 = 30
    decide
  have hzsq : (∑ i, (((![4, 5, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 266 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 9^2 + 12^2 = 266
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_04_03

theorem weighted_04_01_04_03 : b4RawGapContribution ![4, 1, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 4, 3] = b4GapPatternWeight 1 4 3 * 0 :=
      b4GapContribution_from_row 4 1 4 3 0 row_04_01_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_04_03

theorem row_04_01_04_04 : b4RowContribution (![4, 5, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 9, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 9 + 13 = 31
    decide
  have hzsq : (∑ i, (((![4, 5, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 291 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 9^2 + 13^2 = 291
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_04_04

theorem weighted_04_01_04_04 : b4RawGapContribution ![4, 1, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 4, 4] = b4GapPatternWeight 1 4 4 * 0 :=
      b4GapContribution_from_row 4 1 4 4 0 row_04_01_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_04_04

theorem row_04_01_04_05 : b4RowContribution (![4, 5, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 9, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 9 + 14 = 32
    decide
  have hzsq : (∑ i, (((![4, 5, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 318 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 9^2 + 14^2 = 318
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_04_05

theorem weighted_04_01_04_05 : b4RawGapContribution ![4, 1, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 4, 5] = b4GapPatternWeight 1 4 5 * 0 :=
      b4GapContribution_from_row 4 1 4 5 0 row_04_01_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_04_05

theorem row_04_01_04_06 : b4RowContribution (![4, 5, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 9, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 9 + 15 = 33
    decide
  have hzsq : (∑ i, (((![4, 5, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 347 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 9^2 + 15^2 = 347
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_04_06

theorem weighted_04_01_04_06 : b4RawGapContribution ![4, 1, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 4, 6] = b4GapPatternWeight 1 4 6 * 0 :=
      b4GapContribution_from_row 4 1 4 6 0 row_04_01_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_04_06

theorem row_04_01_04_07 : b4RowContribution (![4, 5, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 9, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 9 + 16 = 34
    decide
  have hzsq : (∑ i, (((![4, 5, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 378 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 9^2 + 16^2 = 378
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_04_07

theorem weighted_04_01_04_07 : b4RawGapContribution ![4, 1, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 4, 7] = b4GapPatternWeight 1 4 7 * 0 :=
      b4GapContribution_from_row 4 1 4 7 0 row_04_01_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_04_07

theorem row_04_01_04_08 : b4RowContribution (![4, 5, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 9, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 9 + 17 = 35
    decide
  have hzsq : (∑ i, (((![4, 5, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 411 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 9^2 + 17^2 = 411
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_04_08

theorem weighted_04_01_04_08 : b4RawGapContribution ![4, 1, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 4, 8] = b4GapPatternWeight 1 4 8 * 0 :=
      b4GapContribution_from_row 4 1 4 8 0 row_04_01_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_04_08

theorem row_04_01_04_09 : b4RowContribution (![4, 5, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 9, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 9 + 18 = 36
    decide
  have hzsq : (∑ i, (((![4, 5, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 446 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 9^2 + 18^2 = 446
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_04_09

theorem weighted_04_01_04_09 : b4RawGapContribution ![4, 1, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 4, 9] = b4GapPatternWeight 1 4 9 * 0 :=
      b4GapContribution_from_row 4 1 4 9 0 row_04_01_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_04_09

theorem row_04_01_04_10 : b4RowContribution (![4, 5, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 5, 9, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 5 + 9 + 19 = 37
    decide
  have hzsq : (∑ i, (((![4, 5, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 483 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 5^2 + 9^2 + 19^2 = 483
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_01_04_10

theorem weighted_04_01_04_10 : b4RawGapContribution ![4, 1, 4, 10] = 0 := by
  calc
    b4RawGapContribution ![4, 1, 4, 10] = b4GapPatternWeight 1 4 10 * 0 :=
      b4GapContribution_from_row 4 1 4 10 0 row_04_01_04_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_01_04_10

def dvalues_04_01_04 : Fin 11 → ℕ := ![0, 3960, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_01_04

theorem dblock_04_01_04 : b4GapPatternDBlock 4 1 4 = 3960 := by
  calc
    b4GapPatternDBlock 4 1 4 = ∑ d : Fin 11, dvalues_04_01_04 d := by
      apply b4GapDBlock_of_rows 4 1 4 dvalues_04_01_04
      intro d
      fin_cases d
      · exact weighted_04_01_04_00
      · exact weighted_04_01_04_01
      · exact weighted_04_01_04_02
      · exact weighted_04_01_04_03
      · exact weighted_04_01_04_04
      · exact weighted_04_01_04_05
      · exact weighted_04_01_04_06
      · exact weighted_04_01_04_07
      · exact weighted_04_01_04_08
      · exact weighted_04_01_04_09
      · exact weighted_04_01_04_10
    _ = 3960 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_01_04

end Paper7MomentGapNumeric
