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

def layers_00_08_01_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0], ![1, 3, 6, 10, 15, 21, 28, 36, 45, 54, 61, 66, 69, 70, 69, 66, 61, 54, 45]]
#print axioms Paper7MomentGapNumeric.layers_00_08_01_00

theorem cells_00_08_01_00 : QTableValid (![0, 8, 9, 9] : Fin 4 → ℕ) layers_00_08_01_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_08_01_00

theorem valid_00_08_01_00 :
    SparseRowValid (![0, 8, 9, 9] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_00_08_01_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 8, 9, 9] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 0 + 8 + 9 + 9 = 26
      decide
    have hzsq : (∑ i, (((![0, 8, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 226 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 8^2 + 9^2 + 9^2 = 226
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_08_01_00
#print axioms Paper7MomentGapNumeric.valid_00_08_01_00

def qvalues_00_08_01_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_08_01_00

theorem row_00_08_01_00 : b4RowContribution (![0, 8, 9, 9] : Fin 4 → ℕ) = 61 := by
  calc
    b4RowContribution (![0, 8, 9, 9] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_00_08_01_00) :=
      sparseRow_sound (![0, 8, 9, 9] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_00_08_01_00) valid_00_08_01_00
    _ = 61 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_08_01_00 Q := by
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
        _ = 61 := by decide
#print axioms Paper7MomentGapNumeric.row_00_08_01_00

theorem weighted_00_08_01_00 : b4RawGapContribution ![0, 8, 1, 0] = 732 := by
  calc
    b4RawGapContribution ![0, 8, 1, 0] = b4GapPatternWeight 8 1 0 * 61 :=
      b4GapContribution_from_row 0 8 1 0 61 row_00_08_01_00
    _ = 732 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_01_00

theorem row_00_08_01_01 : b4RowContribution (![0, 8, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 9, 10] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 9 + 10 = 27
    decide
  have hzsq : (∑ i, (((![0, 8, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 245 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 9^2 + 10^2 = 245
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_01_01

theorem weighted_00_08_01_01 : b4RawGapContribution ![0, 8, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 1, 1] = b4GapPatternWeight 8 1 1 * 0 :=
      b4GapContribution_from_row 0 8 1 1 0 row_00_08_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_01_01

theorem row_00_08_01_02 : b4RowContribution (![0, 8, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 9, 11] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 9 + 11 = 28
    decide
  have hzsq : (∑ i, (((![0, 8, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 266 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 9^2 + 11^2 = 266
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_01_02

theorem weighted_00_08_01_02 : b4RawGapContribution ![0, 8, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 1, 2] = b4GapPatternWeight 8 1 2 * 0 :=
      b4GapContribution_from_row 0 8 1 2 0 row_00_08_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_01_02

theorem row_00_08_01_03 : b4RowContribution (![0, 8, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 9, 12] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 9 + 12 = 29
    decide
  have hzsq : (∑ i, (((![0, 8, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 289 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 9^2 + 12^2 = 289
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_01_03

theorem weighted_00_08_01_03 : b4RawGapContribution ![0, 8, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 1, 3] = b4GapPatternWeight 8 1 3 * 0 :=
      b4GapContribution_from_row 0 8 1 3 0 row_00_08_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_01_03

theorem row_00_08_01_04 : b4RowContribution (![0, 8, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 9, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 9 + 13 = 30
    decide
  have hzsq : (∑ i, (((![0, 8, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 314 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 9^2 + 13^2 = 314
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_01_04

theorem weighted_00_08_01_04 : b4RawGapContribution ![0, 8, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 1, 4] = b4GapPatternWeight 8 1 4 * 0 :=
      b4GapContribution_from_row 0 8 1 4 0 row_00_08_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_01_04

theorem row_00_08_01_05 : b4RowContribution (![0, 8, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 9, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 9 + 14 = 31
    decide
  have hzsq : (∑ i, (((![0, 8, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 341 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 9^2 + 14^2 = 341
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_01_05

theorem weighted_00_08_01_05 : b4RawGapContribution ![0, 8, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 1, 5] = b4GapPatternWeight 8 1 5 * 0 :=
      b4GapContribution_from_row 0 8 1 5 0 row_00_08_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_01_05

theorem row_00_08_01_06 : b4RowContribution (![0, 8, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 9, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 9 + 15 = 32
    decide
  have hzsq : (∑ i, (((![0, 8, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 370 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 9^2 + 15^2 = 370
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_01_06

theorem weighted_00_08_01_06 : b4RawGapContribution ![0, 8, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 1, 6] = b4GapPatternWeight 8 1 6 * 0 :=
      b4GapContribution_from_row 0 8 1 6 0 row_00_08_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_01_06

theorem row_00_08_01_07 : b4RowContribution (![0, 8, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 9, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 9 + 16 = 33
    decide
  have hzsq : (∑ i, (((![0, 8, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 401 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 9^2 + 16^2 = 401
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_01_07

theorem weighted_00_08_01_07 : b4RawGapContribution ![0, 8, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 1, 7] = b4GapPatternWeight 8 1 7 * 0 :=
      b4GapContribution_from_row 0 8 1 7 0 row_00_08_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_01_07

theorem row_00_08_01_08 : b4RowContribution (![0, 8, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 9, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 9 + 17 = 34
    decide
  have hzsq : (∑ i, (((![0, 8, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 434 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 9^2 + 17^2 = 434
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_01_08

theorem weighted_00_08_01_08 : b4RawGapContribution ![0, 8, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 1, 8] = b4GapPatternWeight 8 1 8 * 0 :=
      b4GapContribution_from_row 0 8 1 8 0 row_00_08_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_01_08

theorem row_00_08_01_09 : b4RowContribution (![0, 8, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 9, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 9 + 18 = 35
    decide
  have hzsq : (∑ i, (((![0, 8, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 469 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 9^2 + 18^2 = 469
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_01_09

theorem weighted_00_08_01_09 : b4RawGapContribution ![0, 8, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 1, 9] = b4GapPatternWeight 8 1 9 * 0 :=
      b4GapContribution_from_row 0 8 1 9 0 row_00_08_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_01_09

theorem row_00_08_01_10 : b4RowContribution (![0, 8, 9, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 9, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 9 + 19 = 36
    decide
  have hzsq : (∑ i, (((![0, 8, 9, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 506 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 9^2 + 19^2 = 506
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_01_10

theorem weighted_00_08_01_10 : b4RawGapContribution ![0, 8, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 1, 10] = b4GapPatternWeight 8 1 10 * 0 :=
      b4GapContribution_from_row 0 8 1 10 0 row_00_08_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_01_10

theorem row_00_08_01_11 : b4RowContribution (![0, 8, 9, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 9, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 9 + 20 = 37
    decide
  have hzsq : (∑ i, (((![0, 8, 9, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 545 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 9^2 + 20^2 = 545
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_01_11

theorem weighted_00_08_01_11 : b4RawGapContribution ![0, 8, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 1, 11] = b4GapPatternWeight 8 1 11 * 0 :=
      b4GapContribution_from_row 0 8 1 11 0 row_00_08_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_01_11

def dvalues_00_08_01 : Fin 12 → ℕ := ![732, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_08_01

theorem dblock_00_08_01 : b4GapPatternDBlock 0 8 1 = 732 := by
  calc
    b4GapPatternDBlock 0 8 1 = ∑ d : Fin 12, dvalues_00_08_01 d := by
      apply b4GapDBlock_of_rows 0 8 1 dvalues_00_08_01
      intro d
      fin_cases d
      · exact weighted_00_08_01_00
      · exact weighted_00_08_01_01
      · exact weighted_00_08_01_02
      · exact weighted_00_08_01_03
      · exact weighted_00_08_01_04
      · exact weighted_00_08_01_05
      · exact weighted_00_08_01_06
      · exact weighted_00_08_01_07
      · exact weighted_00_08_01_08
      · exact weighted_00_08_01_09
      · exact weighted_00_08_01_10
      · exact weighted_00_08_01_11
    _ = 732 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_08_01

end Paper7MomentGapNumeric
