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

def layers_02_06_01_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 26, 26, 24, 21, 18, 15, 12, 9, 6, 3], ![1, 4, 10, 19, 31, 46, 64, 85, 109, 135, 160, 181, 196, 205, 208, 205, 196, 181, 160]]
#print axioms Paper7MomentGapNumeric.layers_02_06_01_00

theorem cells_02_06_01_00 : QTableValid (![2, 8, 9, 9] : Fin 4 → ℕ) layers_02_06_01_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_06_01_00

theorem valid_02_06_01_00 :
    SparseRowValid (![2, 8, 9, 9] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_02_06_01_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 8, 9, 9] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 2 + 8 + 9 + 9 = 28
      decide
    have hzsq : (∑ i, (((![2, 8, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 230 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 8^2 + 9^2 + 9^2 = 230
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_06_01_00
#print axioms Paper7MomentGapNumeric.valid_02_06_01_00

def qvalues_02_06_01_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_06_01_00

theorem row_02_06_01_00 : b4RowContribution (![2, 8, 9, 9] : Fin 4 → ℕ) = 46 := by
  calc
    b4RowContribution (![2, 8, 9, 9] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_02_06_01_00) :=
      sparseRow_sound (![2, 8, 9, 9] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_02_06_01_00) valid_02_06_01_00
    _ = 46 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_06_01_00 Q := by
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
        _ = 46 := by decide
#print axioms Paper7MomentGapNumeric.row_02_06_01_00

theorem weighted_02_06_01_00 : b4RawGapContribution ![2, 6, 1, 0] = 552 := by
  calc
    b4RawGapContribution ![2, 6, 1, 0] = b4GapPatternWeight 6 1 0 * 46 :=
      b4GapContribution_from_row 2 6 1 0 46 row_02_06_01_00
    _ = 552 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_01_00

theorem row_02_06_01_01 : b4RowContribution (![2, 8, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 9, 10] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 9 + 10 = 29
    decide
  have hzsq : (∑ i, (((![2, 8, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 249 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 9^2 + 10^2 = 249
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_01_01

theorem weighted_02_06_01_01 : b4RawGapContribution ![2, 6, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 1, 1] = b4GapPatternWeight 6 1 1 * 0 :=
      b4GapContribution_from_row 2 6 1 1 0 row_02_06_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_01_01

def layers_02_06_01_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 26, 26, 24, 21, 18, 15, 12, 9, 6, 3], ![1, 4, 10, 19, 31, 46, 64, 85, 109, 135, 161, 185, 205, 220, 229, 232, 229, 220, 205]]
#print axioms Paper7MomentGapNumeric.layers_02_06_01_02

theorem cells_02_06_01_02 : QTableValid (![2, 8, 9, 11] : Fin 4 → ℕ) layers_02_06_01_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_06_01_02

theorem valid_02_06_01_02 :
    SparseRowValid (![2, 8, 9, 11] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_02_06_01_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 8, 9, 11] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 2 + 8 + 9 + 11 = 30
      decide
    have hzsq : (∑ i, (((![2, 8, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 8^2 + 9^2 + 11^2 = 270
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_06_01_02
#print axioms Paper7MomentGapNumeric.valid_02_06_01_02

def qvalues_02_06_01_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_06_01_02

theorem row_02_06_01_02 : b4RowContribution (![2, 8, 9, 11] : Fin 4 → ℕ) = 64 := by
  calc
    b4RowContribution (![2, 8, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_02_06_01_02) :=
      sparseRow_sound (![2, 8, 9, 11] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_02_06_01_02) valid_02_06_01_02
    _ = 64 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_06_01_02 Q := by
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
        _ = 64 := by decide
#print axioms Paper7MomentGapNumeric.row_02_06_01_02

theorem weighted_02_06_01_02 : b4RawGapContribution ![2, 6, 1, 2] = 1536 := by
  calc
    b4RawGapContribution ![2, 6, 1, 2] = b4GapPatternWeight 6 1 2 * 64 :=
      b4GapContribution_from_row 2 6 1 2 64 row_02_06_01_02
    _ = 1536 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_01_02

theorem row_02_06_01_03 : b4RowContribution (![2, 8, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 9, 12] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 9 + 12 = 31
    decide
  have hzsq : (∑ i, (((![2, 8, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 293 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 9^2 + 12^2 = 293
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_01_03

theorem weighted_02_06_01_03 : b4RawGapContribution ![2, 6, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 1, 3] = b4GapPatternWeight 6 1 3 * 0 :=
      b4GapContribution_from_row 2 6 1 3 0 row_02_06_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_01_03

theorem row_02_06_01_04 : b4RowContribution (![2, 8, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 9, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 9 + 13 = 32
    decide
  have hzsq : (∑ i, (((![2, 8, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 318 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 9^2 + 13^2 = 318
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_01_04

theorem weighted_02_06_01_04 : b4RawGapContribution ![2, 6, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 1, 4] = b4GapPatternWeight 6 1 4 * 0 :=
      b4GapContribution_from_row 2 6 1 4 0 row_02_06_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_01_04

theorem row_02_06_01_05 : b4RowContribution (![2, 8, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 9, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 9 + 14 = 33
    decide
  have hzsq : (∑ i, (((![2, 8, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 345 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 9^2 + 14^2 = 345
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_01_05

theorem weighted_02_06_01_05 : b4RawGapContribution ![2, 6, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 1, 5] = b4GapPatternWeight 6 1 5 * 0 :=
      b4GapContribution_from_row 2 6 1 5 0 row_02_06_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_01_05

theorem row_02_06_01_06 : b4RowContribution (![2, 8, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 9, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 9 + 15 = 34
    decide
  have hzsq : (∑ i, (((![2, 8, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 374 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 9^2 + 15^2 = 374
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_01_06

theorem weighted_02_06_01_06 : b4RawGapContribution ![2, 6, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 1, 6] = b4GapPatternWeight 6 1 6 * 0 :=
      b4GapContribution_from_row 2 6 1 6 0 row_02_06_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_01_06

theorem row_02_06_01_07 : b4RowContribution (![2, 8, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 9, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 9 + 16 = 35
    decide
  have hzsq : (∑ i, (((![2, 8, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 405 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 9^2 + 16^2 = 405
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_01_07

theorem weighted_02_06_01_07 : b4RawGapContribution ![2, 6, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 1, 7] = b4GapPatternWeight 6 1 7 * 0 :=
      b4GapContribution_from_row 2 6 1 7 0 row_02_06_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_01_07

theorem row_02_06_01_08 : b4RowContribution (![2, 8, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 9, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 9 + 17 = 36
    decide
  have hzsq : (∑ i, (((![2, 8, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 438 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 9^2 + 17^2 = 438
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_01_08

theorem weighted_02_06_01_08 : b4RawGapContribution ![2, 6, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 1, 8] = b4GapPatternWeight 6 1 8 * 0 :=
      b4GapContribution_from_row 2 6 1 8 0 row_02_06_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_01_08

theorem row_02_06_01_09 : b4RowContribution (![2, 8, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 9, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 9 + 18 = 37
    decide
  have hzsq : (∑ i, (((![2, 8, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 473 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 9^2 + 18^2 = 473
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_01_09

theorem weighted_02_06_01_09 : b4RawGapContribution ![2, 6, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 1, 9] = b4GapPatternWeight 6 1 9 * 0 :=
      b4GapContribution_from_row 2 6 1 9 0 row_02_06_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_01_09

def dvalues_02_06_01 : Fin 10 → ℕ := ![552, 0, 1536, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_06_01

theorem dblock_02_06_01 : b4GapPatternDBlock 2 6 1 = 2088 := by
  calc
    b4GapPatternDBlock 2 6 1 = ∑ d : Fin 10, dvalues_02_06_01 d := by
      apply b4GapDBlock_of_rows 2 6 1 dvalues_02_06_01
      intro d
      fin_cases d
      · exact weighted_02_06_01_00
      · exact weighted_02_06_01_01
      · exact weighted_02_06_01_02
      · exact weighted_02_06_01_03
      · exact weighted_02_06_01_04
      · exact weighted_02_06_01_05
      · exact weighted_02_06_01_06
      · exact weighted_02_06_01_07
      · exact weighted_02_06_01_08
      · exact weighted_02_06_01_09
    _ = 2088 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_06_01

end Paper7MomentGapNumeric
