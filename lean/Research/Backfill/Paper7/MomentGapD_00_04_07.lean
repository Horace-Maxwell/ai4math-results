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

theorem row_00_04_07_00 : b4RowContribution (![0, 4, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 11, 11] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 11 + 11 = 26
    decide
  have hzsq : (∑ i, (((![0, 4, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 258 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 11^2 + 11^2 = 258
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_07_00

theorem weighted_00_04_07_00 : b4RawGapContribution ![0, 4, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 7, 0] = b4GapPatternWeight 4 7 0 * 0 :=
      b4GapContribution_from_row 0 4 7 0 0 row_00_04_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_07_00

def layers_00_04_07_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 35, 40, 45, 50, 54, 56, 56, 54, 50, 45, 40]]
#print axioms Paper7MomentGapNumeric.layers_00_04_07_01

theorem cells_00_04_07_01 : QTableValid (![0, 4, 11, 12] : Fin 4 → ℕ) layers_00_04_07_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_04_07_01

theorem valid_00_04_07_01 :
    SparseRowValid (![0, 4, 11, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_04_07_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 4, 11, 12] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 0 + 4 + 11 + 12 = 27
      decide
    have hzsq : (∑ i, (((![0, 4, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 281 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 4^2 + 11^2 + 12^2 = 281
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_04_07_01
#print axioms Paper7MomentGapNumeric.valid_00_04_07_01

def qvalues_00_04_07_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_04_07_01

theorem row_00_04_07_01 : b4RowContribution (![0, 4, 11, 12] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![0, 4, 11, 12] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_00_04_07_01) :=
      sparseRow_sound (![0, 4, 11, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_04_07_01) valid_00_04_07_01
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_04_07_01 Q := by
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
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_00_04_07_01

theorem weighted_00_04_07_01 : b4RawGapContribution ![0, 4, 7, 1] = 480 := by
  calc
    b4RawGapContribution ![0, 4, 7, 1] = b4GapPatternWeight 4 7 1 * 20 :=
      b4GapContribution_from_row 0 4 7 1 20 row_00_04_07_01
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_07_01

theorem row_00_04_07_02 : b4RowContribution (![0, 4, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 11, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 11 + 13 = 28
    decide
  have hzsq : (∑ i, (((![0, 4, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 11^2 + 13^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_07_02

theorem weighted_00_04_07_02 : b4RawGapContribution ![0, 4, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 7, 2] = b4GapPatternWeight 4 7 2 * 0 :=
      b4GapContribution_from_row 0 4 7 2 0 row_00_04_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_07_02

theorem row_00_04_07_03 : b4RowContribution (![0, 4, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 11, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 11 + 14 = 29
    decide
  have hzsq : (∑ i, (((![0, 4, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 333 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 11^2 + 14^2 = 333
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_07_03

theorem weighted_00_04_07_03 : b4RawGapContribution ![0, 4, 7, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 7, 3] = b4GapPatternWeight 4 7 3 * 0 :=
      b4GapContribution_from_row 0 4 7 3 0 row_00_04_07_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_07_03

theorem row_00_04_07_04 : b4RowContribution (![0, 4, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 11, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 11 + 15 = 30
    decide
  have hzsq : (∑ i, (((![0, 4, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 362 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 11^2 + 15^2 = 362
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_07_04

theorem weighted_00_04_07_04 : b4RawGapContribution ![0, 4, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 7, 4] = b4GapPatternWeight 4 7 4 * 0 :=
      b4GapContribution_from_row 0 4 7 4 0 row_00_04_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_07_04

theorem row_00_04_07_05 : b4RowContribution (![0, 4, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 11, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 11 + 16 = 31
    decide
  have hzsq : (∑ i, (((![0, 4, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 393 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 11^2 + 16^2 = 393
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_07_05

theorem weighted_00_04_07_05 : b4RawGapContribution ![0, 4, 7, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 7, 5] = b4GapPatternWeight 4 7 5 * 0 :=
      b4GapContribution_from_row 0 4 7 5 0 row_00_04_07_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_07_05

theorem row_00_04_07_06 : b4RowContribution (![0, 4, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 11, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 11 + 17 = 32
    decide
  have hzsq : (∑ i, (((![0, 4, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 426 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 11^2 + 17^2 = 426
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_07_06

theorem weighted_00_04_07_06 : b4RawGapContribution ![0, 4, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 7, 6] = b4GapPatternWeight 4 7 6 * 0 :=
      b4GapContribution_from_row 0 4 7 6 0 row_00_04_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_07_06

theorem row_00_04_07_07 : b4RowContribution (![0, 4, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 11, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 11 + 18 = 33
    decide
  have hzsq : (∑ i, (((![0, 4, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 461 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 11^2 + 18^2 = 461
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_07_07

theorem weighted_00_04_07_07 : b4RawGapContribution ![0, 4, 7, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 7, 7] = b4GapPatternWeight 4 7 7 * 0 :=
      b4GapContribution_from_row 0 4 7 7 0 row_00_04_07_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_07_07

theorem row_00_04_07_08 : b4RowContribution (![0, 4, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 11, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 11 + 19 = 34
    decide
  have hzsq : (∑ i, (((![0, 4, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 498 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 11^2 + 19^2 = 498
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_07_08

theorem weighted_00_04_07_08 : b4RawGapContribution ![0, 4, 7, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 7, 8] = b4GapPatternWeight 4 7 8 * 0 :=
      b4GapContribution_from_row 0 4 7 8 0 row_00_04_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_07_08

theorem row_00_04_07_09 : b4RowContribution (![0, 4, 11, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 11, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 11 + 20 = 35
    decide
  have hzsq : (∑ i, (((![0, 4, 11, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 537 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 11^2 + 20^2 = 537
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_07_09

theorem weighted_00_04_07_09 : b4RawGapContribution ![0, 4, 7, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 7, 9] = b4GapPatternWeight 4 7 9 * 0 :=
      b4GapContribution_from_row 0 4 7 9 0 row_00_04_07_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_07_09

theorem row_00_04_07_10 : b4RowContribution (![0, 4, 11, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 11, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 11 + 21 = 36
    decide
  have hzsq : (∑ i, (((![0, 4, 11, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 578 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 11^2 + 21^2 = 578
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_07_10

theorem weighted_00_04_07_10 : b4RawGapContribution ![0, 4, 7, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 7, 10] = b4GapPatternWeight 4 7 10 * 0 :=
      b4GapContribution_from_row 0 4 7 10 0 row_00_04_07_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_07_10

theorem row_00_04_07_11 : b4RowContribution (![0, 4, 11, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 4, 11, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 4 + 11 + 22 = 37
    decide
  have hzsq : (∑ i, (((![0, 4, 11, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 621 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 4^2 + 11^2 + 22^2 = 621
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_04_07_11

theorem weighted_00_04_07_11 : b4RawGapContribution ![0, 4, 7, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 4, 7, 11] = b4GapPatternWeight 4 7 11 * 0 :=
      b4GapContribution_from_row 0 4 7 11 0 row_00_04_07_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_04_07_11

def dvalues_00_04_07 : Fin 12 → ℕ := ![0, 480, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_04_07

theorem dblock_00_04_07 : b4GapPatternDBlock 0 4 7 = 480 := by
  calc
    b4GapPatternDBlock 0 4 7 = ∑ d : Fin 12, dvalues_00_04_07 d := by
      apply b4GapDBlock_of_rows 0 4 7 dvalues_00_04_07
      intro d
      fin_cases d
      · exact weighted_00_04_07_00
      · exact weighted_00_04_07_01
      · exact weighted_00_04_07_02
      · exact weighted_00_04_07_03
      · exact weighted_00_04_07_04
      · exact weighted_00_04_07_05
      · exact weighted_00_04_07_06
      · exact weighted_00_04_07_07
      · exact weighted_00_04_07_08
      · exact weighted_00_04_07_09
      · exact weighted_00_04_07_10
      · exact weighted_00_04_07_11
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_04_07

end Paper7MomentGapNumeric
