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

theorem row_02_02_07_00 : b4RowContribution (![2, 4, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 11, 11] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 11 + 11 = 28
    decide
  have hzsq : (∑ i, (((![2, 4, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 262 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 11^2 + 11^2 = 262
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_07_00

theorem weighted_02_02_07_00 : b4RawGapContribution ![2, 2, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 7, 0] = b4GapPatternWeight 2 7 0 * 0 :=
      b4GapContribution_from_row 2 2 7 0 0 row_02_02_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_07_00

def layers_02_02_07_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 14, 15, 15, 15, 15, 15, 15, 14, 12, 9, 6, 3, 1, 0], ![1, 4, 10, 19, 31, 45, 60, 75, 90, 105, 120, 135, 149, 160, 166, 166, 160, 149, 135]]
#print axioms Paper7MomentGapNumeric.layers_02_02_07_01

theorem cells_02_02_07_01 : QTableValid (![2, 4, 11, 12] : Fin 4 → ℕ) layers_02_02_07_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_02_07_01

theorem valid_02_02_07_01 :
    SparseRowValid (![2, 4, 11, 12] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_02_02_07_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 4, 11, 12] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 2 + 4 + 11 + 12 = 29
      decide
    have hzsq : (∑ i, (((![2, 4, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 285 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 4^2 + 11^2 + 12^2 = 285
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_02_07_01
#print axioms Paper7MomentGapNumeric.valid_02_02_07_01

def qvalues_02_02_07_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_02_07_01

theorem row_02_02_07_01 : b4RowContribution (![2, 4, 11, 12] : Fin 4 → ℕ) = 60 := by
  calc
    b4RowContribution (![2, 4, 11, 12] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_02_02_07_01) :=
      sparseRow_sound (![2, 4, 11, 12] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_02_02_07_01) valid_02_02_07_01
    _ = 60 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_02_07_01 Q := by
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
        _ = 60 := by decide
#print axioms Paper7MomentGapNumeric.row_02_02_07_01

theorem weighted_02_02_07_01 : b4RawGapContribution ![2, 2, 7, 1] = 1440 := by
  calc
    b4RawGapContribution ![2, 2, 7, 1] = b4GapPatternWeight 2 7 1 * 60 :=
      b4GapContribution_from_row 2 2 7 1 60 row_02_02_07_01
    _ = 1440 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_07_01

theorem row_02_02_07_02 : b4RowContribution (![2, 4, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 11, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 11 + 13 = 30
    decide
  have hzsq : (∑ i, (((![2, 4, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 310 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 11^2 + 13^2 = 310
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_07_02

theorem weighted_02_02_07_02 : b4RawGapContribution ![2, 2, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 7, 2] = b4GapPatternWeight 2 7 2 * 0 :=
      b4GapContribution_from_row 2 2 7 2 0 row_02_02_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_07_02

theorem row_02_02_07_03 : b4RowContribution (![2, 4, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 11, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 11 + 14 = 31
    decide
  have hzsq : (∑ i, (((![2, 4, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 337 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 11^2 + 14^2 = 337
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_07_03

theorem weighted_02_02_07_03 : b4RawGapContribution ![2, 2, 7, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 7, 3] = b4GapPatternWeight 2 7 3 * 0 :=
      b4GapContribution_from_row 2 2 7 3 0 row_02_02_07_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_07_03

theorem row_02_02_07_04 : b4RowContribution (![2, 4, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 11, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 11 + 15 = 32
    decide
  have hzsq : (∑ i, (((![2, 4, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 366 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 11^2 + 15^2 = 366
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_07_04

theorem weighted_02_02_07_04 : b4RawGapContribution ![2, 2, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 7, 4] = b4GapPatternWeight 2 7 4 * 0 :=
      b4GapContribution_from_row 2 2 7 4 0 row_02_02_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_07_04

theorem row_02_02_07_05 : b4RowContribution (![2, 4, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 11, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 11 + 16 = 33
    decide
  have hzsq : (∑ i, (((![2, 4, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 397 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 11^2 + 16^2 = 397
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_07_05

theorem weighted_02_02_07_05 : b4RawGapContribution ![2, 2, 7, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 7, 5] = b4GapPatternWeight 2 7 5 * 0 :=
      b4GapContribution_from_row 2 2 7 5 0 row_02_02_07_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_07_05

theorem row_02_02_07_06 : b4RowContribution (![2, 4, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 11, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 11 + 17 = 34
    decide
  have hzsq : (∑ i, (((![2, 4, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 430 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 11^2 + 17^2 = 430
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_07_06

theorem weighted_02_02_07_06 : b4RawGapContribution ![2, 2, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 7, 6] = b4GapPatternWeight 2 7 6 * 0 :=
      b4GapContribution_from_row 2 2 7 6 0 row_02_02_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_07_06

theorem row_02_02_07_07 : b4RowContribution (![2, 4, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 11, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 11 + 18 = 35
    decide
  have hzsq : (∑ i, (((![2, 4, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 465 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 11^2 + 18^2 = 465
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_07_07

theorem weighted_02_02_07_07 : b4RawGapContribution ![2, 2, 7, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 7, 7] = b4GapPatternWeight 2 7 7 * 0 :=
      b4GapContribution_from_row 2 2 7 7 0 row_02_02_07_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_07_07

theorem row_02_02_07_08 : b4RowContribution (![2, 4, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 11, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 11 + 19 = 36
    decide
  have hzsq : (∑ i, (((![2, 4, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 502 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 11^2 + 19^2 = 502
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_07_08

theorem weighted_02_02_07_08 : b4RawGapContribution ![2, 2, 7, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 7, 8] = b4GapPatternWeight 2 7 8 * 0 :=
      b4GapContribution_from_row 2 2 7 8 0 row_02_02_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_07_08

theorem row_02_02_07_09 : b4RowContribution (![2, 4, 11, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 4, 11, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 4 + 11 + 20 = 37
    decide
  have hzsq : (∑ i, (((![2, 4, 11, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 541 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 4^2 + 11^2 + 20^2 = 541
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_02_07_09

theorem weighted_02_02_07_09 : b4RawGapContribution ![2, 2, 7, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 2, 7, 9] = b4GapPatternWeight 2 7 9 * 0 :=
      b4GapContribution_from_row 2 2 7 9 0 row_02_02_07_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_02_07_09

def dvalues_02_02_07 : Fin 10 → ℕ := ![0, 1440, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_02_07

theorem dblock_02_02_07 : b4GapPatternDBlock 2 2 7 = 1440 := by
  calc
    b4GapPatternDBlock 2 2 7 = ∑ d : Fin 10, dvalues_02_02_07 d := by
      apply b4GapDBlock_of_rows 2 2 7 dvalues_02_02_07
      intro d
      fin_cases d
      · exact weighted_02_02_07_00
      · exact weighted_02_02_07_01
      · exact weighted_02_02_07_02
      · exact weighted_02_02_07_03
      · exact weighted_02_02_07_04
      · exact weighted_02_02_07_05
      · exact weighted_02_02_07_06
      · exact weighted_02_02_07_07
      · exact weighted_02_02_07_08
      · exact weighted_02_02_07_09
    _ = 1440 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_02_07

end Paper7MomentGapNumeric
