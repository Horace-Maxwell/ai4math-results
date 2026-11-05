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

theorem row_00_03_08_00 : b4RowContribution (![0, 3, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 11, 11] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 11 + 11 = 25
    decide
  have hzsq : (∑ i, (((![0, 3, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 251 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 11^2 + 11^2 = 251
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_08_00

theorem weighted_00_03_08_00 : b4RawGapContribution ![0, 3, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 8, 0] = b4GapPatternWeight 3 8 0 * 0 :=
      b4GapContribution_from_row 0 3 8 0 0 row_00_03_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_08_00

def layers_00_03_08_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 30, 34, 38, 42, 45, 46, 45, 42, 38, 34, 30]]
#print axioms Paper7MomentGapNumeric.layers_00_03_08_01

theorem cells_00_03_08_01 : QTableValid (![0, 3, 11, 12] : Fin 4 → ℕ) layers_00_03_08_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_03_08_01

theorem valid_00_03_08_01 :
    SparseRowValid (![0, 3, 11, 12] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_00_03_08_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 3, 11, 12] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 0 + 3 + 11 + 12 = 26
      decide
    have hzsq : (∑ i, (((![0, 3, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 274 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 3^2 + 11^2 + 12^2 = 274
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_03_08_01
#print axioms Paper7MomentGapNumeric.valid_00_03_08_01

def qvalues_00_03_08_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_03_08_01

theorem row_00_03_08_01 : b4RowContribution (![0, 3, 11, 12] : Fin 4 → ℕ) = 38 := by
  calc
    b4RowContribution (![0, 3, 11, 12] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_00_03_08_01) :=
      sparseRow_sound (![0, 3, 11, 12] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_00_03_08_01) valid_00_03_08_01
    _ = 38 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_03_08_01 Q := by
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
        _ = 38 := by decide
#print axioms Paper7MomentGapNumeric.row_00_03_08_01

theorem weighted_00_03_08_01 : b4RawGapContribution ![0, 3, 8, 1] = 912 := by
  calc
    b4RawGapContribution ![0, 3, 8, 1] = b4GapPatternWeight 3 8 1 * 38 :=
      b4GapContribution_from_row 0 3 8 1 38 row_00_03_08_01
    _ = 912 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_08_01

theorem row_00_03_08_02 : b4RowContribution (![0, 3, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 11, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 11 + 13 = 27
    decide
  have hzsq : (∑ i, (((![0, 3, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 299 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 11^2 + 13^2 = 299
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_08_02

theorem weighted_00_03_08_02 : b4RawGapContribution ![0, 3, 8, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 8, 2] = b4GapPatternWeight 3 8 2 * 0 :=
      b4GapContribution_from_row 0 3 8 2 0 row_00_03_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_08_02

theorem row_00_03_08_03 : b4RowContribution (![0, 3, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 11, 14] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 11 + 14 = 28
    decide
  have hzsq : (∑ i, (((![0, 3, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 326 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 11^2 + 14^2 = 326
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_08_03

theorem weighted_00_03_08_03 : b4RawGapContribution ![0, 3, 8, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 8, 3] = b4GapPatternWeight 3 8 3 * 0 :=
      b4GapContribution_from_row 0 3 8 3 0 row_00_03_08_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_08_03

theorem row_00_03_08_04 : b4RowContribution (![0, 3, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 11, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 11 + 15 = 29
    decide
  have hzsq : (∑ i, (((![0, 3, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 355 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 11^2 + 15^2 = 355
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_08_04

theorem weighted_00_03_08_04 : b4RawGapContribution ![0, 3, 8, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 8, 4] = b4GapPatternWeight 3 8 4 * 0 :=
      b4GapContribution_from_row 0 3 8 4 0 row_00_03_08_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_08_04

theorem row_00_03_08_05 : b4RowContribution (![0, 3, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 11, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 11 + 16 = 30
    decide
  have hzsq : (∑ i, (((![0, 3, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 386 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 11^2 + 16^2 = 386
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_08_05

theorem weighted_00_03_08_05 : b4RawGapContribution ![0, 3, 8, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 8, 5] = b4GapPatternWeight 3 8 5 * 0 :=
      b4GapContribution_from_row 0 3 8 5 0 row_00_03_08_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_08_05

theorem row_00_03_08_06 : b4RowContribution (![0, 3, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 11, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 11 + 17 = 31
    decide
  have hzsq : (∑ i, (((![0, 3, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 419 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 11^2 + 17^2 = 419
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_08_06

theorem weighted_00_03_08_06 : b4RawGapContribution ![0, 3, 8, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 8, 6] = b4GapPatternWeight 3 8 6 * 0 :=
      b4GapContribution_from_row 0 3 8 6 0 row_00_03_08_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_08_06

theorem row_00_03_08_07 : b4RowContribution (![0, 3, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 11, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 11 + 18 = 32
    decide
  have hzsq : (∑ i, (((![0, 3, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 454 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 11^2 + 18^2 = 454
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_08_07

theorem weighted_00_03_08_07 : b4RawGapContribution ![0, 3, 8, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 8, 7] = b4GapPatternWeight 3 8 7 * 0 :=
      b4GapContribution_from_row 0 3 8 7 0 row_00_03_08_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_08_07

theorem row_00_03_08_08 : b4RowContribution (![0, 3, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 11, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 11 + 19 = 33
    decide
  have hzsq : (∑ i, (((![0, 3, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 491 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 11^2 + 19^2 = 491
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_08_08

theorem weighted_00_03_08_08 : b4RawGapContribution ![0, 3, 8, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 8, 8] = b4GapPatternWeight 3 8 8 * 0 :=
      b4GapContribution_from_row 0 3 8 8 0 row_00_03_08_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_08_08

theorem row_00_03_08_09 : b4RowContribution (![0, 3, 11, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 11, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 11 + 20 = 34
    decide
  have hzsq : (∑ i, (((![0, 3, 11, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 530 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 11^2 + 20^2 = 530
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_08_09

theorem weighted_00_03_08_09 : b4RawGapContribution ![0, 3, 8, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 8, 9] = b4GapPatternWeight 3 8 9 * 0 :=
      b4GapContribution_from_row 0 3 8 9 0 row_00_03_08_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_08_09

theorem row_00_03_08_10 : b4RowContribution (![0, 3, 11, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 11, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 11 + 21 = 35
    decide
  have hzsq : (∑ i, (((![0, 3, 11, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 571 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 11^2 + 21^2 = 571
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_08_10

theorem weighted_00_03_08_10 : b4RawGapContribution ![0, 3, 8, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 8, 10] = b4GapPatternWeight 3 8 10 * 0 :=
      b4GapContribution_from_row 0 3 8 10 0 row_00_03_08_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_08_10

theorem row_00_03_08_11 : b4RowContribution (![0, 3, 11, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 11, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 11 + 22 = 36
    decide
  have hzsq : (∑ i, (((![0, 3, 11, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 614 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 11^2 + 22^2 = 614
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_08_11

theorem weighted_00_03_08_11 : b4RawGapContribution ![0, 3, 8, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 8, 11] = b4GapPatternWeight 3 8 11 * 0 :=
      b4GapContribution_from_row 0 3 8 11 0 row_00_03_08_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_08_11

theorem row_00_03_08_12 : b4RowContribution (![0, 3, 11, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 3, 11, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 3 + 11 + 23 = 37
    decide
  have hzsq : (∑ i, (((![0, 3, 11, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 659 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 3^2 + 11^2 + 23^2 = 659
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_03_08_12

theorem weighted_00_03_08_12 : b4RawGapContribution ![0, 3, 8, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 3, 8, 12] = b4GapPatternWeight 3 8 12 * 0 :=
      b4GapContribution_from_row 0 3 8 12 0 row_00_03_08_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_03_08_12

def dvalues_00_03_08 : Fin 13 → ℕ := ![0, 912, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_03_08

theorem dblock_00_03_08 : b4GapPatternDBlock 0 3 8 = 912 := by
  calc
    b4GapPatternDBlock 0 3 8 = ∑ d : Fin 13, dvalues_00_03_08 d := by
      apply b4GapDBlock_of_rows 0 3 8 dvalues_00_03_08
      intro d
      fin_cases d
      · exact weighted_00_03_08_00
      · exact weighted_00_03_08_01
      · exact weighted_00_03_08_02
      · exact weighted_00_03_08_03
      · exact weighted_00_03_08_04
      · exact weighted_00_03_08_05
      · exact weighted_00_03_08_06
      · exact weighted_00_03_08_07
      · exact weighted_00_03_08_08
      · exact weighted_00_03_08_09
      · exact weighted_00_03_08_10
      · exact weighted_00_03_08_11
      · exact weighted_00_03_08_12
    _ = 912 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_03_08

end Paper7MomentGapNumeric
