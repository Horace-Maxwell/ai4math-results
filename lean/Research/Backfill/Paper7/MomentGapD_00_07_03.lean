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

theorem row_00_07_03_00 : b4RowContribution (![0, 7, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 10, 10] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 10 + 10 = 27
    decide
  have hzsq : (∑ i, (((![0, 7, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 249 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 10^2 + 10^2 = 249
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_03_00

theorem weighted_00_07_03_00 : b4RawGapContribution ![0, 7, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 3, 0] = b4GapPatternWeight 7 3 0 * 0 :=
      b4GapContribution_from_row 0 7 3 0 0 row_00_07_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_03_00

def layers_00_07_03_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 8, 8, 8, 7, 6, 5, 4, 3, 2, 1, 0], ![1, 3, 6, 10, 15, 21, 28, 36, 44, 52, 60, 67, 72, 75, 76, 75, 72, 67, 60]]
#print axioms Paper7MomentGapNumeric.layers_00_07_03_01

theorem cells_00_07_03_01 : QTableValid (![0, 7, 10, 11] : Fin 4 → ℕ) layers_00_07_03_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_07_03_01

theorem valid_00_07_03_01 :
    SparseRowValid (![0, 7, 10, 11] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_07_03_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 7, 10, 11] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 0 + 7 + 10 + 11 = 28
      decide
    have hzsq : (∑ i, (((![0, 7, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 270 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 7^2 + 10^2 + 11^2 = 270
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_07_03_01
#print axioms Paper7MomentGapNumeric.valid_00_07_03_01

def qvalues_00_07_03_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_07_03_01

theorem row_00_07_03_01 : b4RowContribution (![0, 7, 10, 11] : Fin 4 → ℕ) = 52 := by
  calc
    b4RowContribution (![0, 7, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_00_07_03_01) :=
      sparseRow_sound (![0, 7, 10, 11] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_00_07_03_01) valid_00_07_03_01
    _ = 52 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_07_03_01 Q := by
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
        _ = 52 := by decide
#print axioms Paper7MomentGapNumeric.row_00_07_03_01

theorem weighted_00_07_03_01 : b4RawGapContribution ![0, 7, 3, 1] = 1248 := by
  calc
    b4RawGapContribution ![0, 7, 3, 1] = b4GapPatternWeight 7 3 1 * 52 :=
      b4GapContribution_from_row 0 7 3 1 52 row_00_07_03_01
    _ = 1248 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_03_01

theorem row_00_07_03_02 : b4RowContribution (![0, 7, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 10, 12] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 10 + 12 = 29
    decide
  have hzsq : (∑ i, (((![0, 7, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 293 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 10^2 + 12^2 = 293
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_03_02

theorem weighted_00_07_03_02 : b4RawGapContribution ![0, 7, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 3, 2] = b4GapPatternWeight 7 3 2 * 0 :=
      b4GapContribution_from_row 0 7 3 2 0 row_00_07_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_03_02

theorem row_00_07_03_03 : b4RowContribution (![0, 7, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 10, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 10 + 13 = 30
    decide
  have hzsq : (∑ i, (((![0, 7, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 318 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 10^2 + 13^2 = 318
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_03_03

theorem weighted_00_07_03_03 : b4RawGapContribution ![0, 7, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 3, 3] = b4GapPatternWeight 7 3 3 * 0 :=
      b4GapContribution_from_row 0 7 3 3 0 row_00_07_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_03_03

theorem row_00_07_03_04 : b4RowContribution (![0, 7, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 10, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 10 + 14 = 31
    decide
  have hzsq : (∑ i, (((![0, 7, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 345 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 10^2 + 14^2 = 345
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_03_04

theorem weighted_00_07_03_04 : b4RawGapContribution ![0, 7, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 3, 4] = b4GapPatternWeight 7 3 4 * 0 :=
      b4GapContribution_from_row 0 7 3 4 0 row_00_07_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_03_04

theorem row_00_07_03_05 : b4RowContribution (![0, 7, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 10, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 10 + 15 = 32
    decide
  have hzsq : (∑ i, (((![0, 7, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 374 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 10^2 + 15^2 = 374
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_03_05

theorem weighted_00_07_03_05 : b4RawGapContribution ![0, 7, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 3, 5] = b4GapPatternWeight 7 3 5 * 0 :=
      b4GapContribution_from_row 0 7 3 5 0 row_00_07_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_03_05

theorem row_00_07_03_06 : b4RowContribution (![0, 7, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 10, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 10 + 16 = 33
    decide
  have hzsq : (∑ i, (((![0, 7, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 405 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 10^2 + 16^2 = 405
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_03_06

theorem weighted_00_07_03_06 : b4RawGapContribution ![0, 7, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 3, 6] = b4GapPatternWeight 7 3 6 * 0 :=
      b4GapContribution_from_row 0 7 3 6 0 row_00_07_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_03_06

theorem row_00_07_03_07 : b4RowContribution (![0, 7, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 10, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 10 + 17 = 34
    decide
  have hzsq : (∑ i, (((![0, 7, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 438 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 10^2 + 17^2 = 438
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_03_07

theorem weighted_00_07_03_07 : b4RawGapContribution ![0, 7, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 3, 7] = b4GapPatternWeight 7 3 7 * 0 :=
      b4GapContribution_from_row 0 7 3 7 0 row_00_07_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_03_07

theorem row_00_07_03_08 : b4RowContribution (![0, 7, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 10, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 10 + 18 = 35
    decide
  have hzsq : (∑ i, (((![0, 7, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 473 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 10^2 + 18^2 = 473
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_03_08

theorem weighted_00_07_03_08 : b4RawGapContribution ![0, 7, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 3, 8] = b4GapPatternWeight 7 3 8 * 0 :=
      b4GapContribution_from_row 0 7 3 8 0 row_00_07_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_03_08

theorem row_00_07_03_09 : b4RowContribution (![0, 7, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 10, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 10 + 19 = 36
    decide
  have hzsq : (∑ i, (((![0, 7, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 510 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 10^2 + 19^2 = 510
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_03_09

theorem weighted_00_07_03_09 : b4RawGapContribution ![0, 7, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 3, 9] = b4GapPatternWeight 7 3 9 * 0 :=
      b4GapContribution_from_row 0 7 3 9 0 row_00_07_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_03_09

theorem row_00_07_03_10 : b4RowContribution (![0, 7, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 7, 10, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 7 + 10 + 20 = 37
    decide
  have hzsq : (∑ i, (((![0, 7, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 549 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 7^2 + 10^2 + 20^2 = 549
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_07_03_10

theorem weighted_00_07_03_10 : b4RawGapContribution ![0, 7, 3, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 7, 3, 10] = b4GapPatternWeight 7 3 10 * 0 :=
      b4GapContribution_from_row 0 7 3 10 0 row_00_07_03_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_07_03_10

def dvalues_00_07_03 : Fin 11 → ℕ := ![0, 1248, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_07_03

theorem dblock_00_07_03 : b4GapPatternDBlock 0 7 3 = 1248 := by
  calc
    b4GapPatternDBlock 0 7 3 = ∑ d : Fin 11, dvalues_00_07_03 d := by
      apply b4GapDBlock_of_rows 0 7 3 dvalues_00_07_03
      intro d
      fin_cases d
      · exact weighted_00_07_03_00
      · exact weighted_00_07_03_01
      · exact weighted_00_07_03_02
      · exact weighted_00_07_03_03
      · exact weighted_00_07_03_04
      · exact weighted_00_07_03_05
      · exact weighted_00_07_03_06
      · exact weighted_00_07_03_07
      · exact weighted_00_07_03_08
      · exact weighted_00_07_03_09
      · exact weighted_00_07_03_10
    _ = 1248 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_07_03

end Paper7MomentGapNumeric
