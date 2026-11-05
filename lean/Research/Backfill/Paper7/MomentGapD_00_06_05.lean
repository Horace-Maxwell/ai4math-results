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

def layers_00_06_05_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 7, 7, 7, 7, 6, 5, 4, 3, 2, 1, 0], ![1, 3, 6, 10, 15, 21, 28, 35, 42, 49, 56, 63, 68, 71, 72, 71, 68, 63, 56]]
#print axioms Paper7MomentGapNumeric.layers_00_06_05_00

theorem cells_00_06_05_00 : QTableValid (![0, 6, 11, 11] : Fin 4 → ℕ) layers_00_06_05_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_06_05_00

theorem valid_00_06_05_00 :
    SparseRowValid (![0, 6, 11, 11] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_06_05_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 6, 11, 11] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 0 + 6 + 11 + 11 = 28
      decide
    have hzsq : (∑ i, (((![0, 6, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 278 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 6^2 + 11^2 + 11^2 = 278
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_06_05_00
#print axioms Paper7MomentGapNumeric.valid_00_06_05_00

def qvalues_00_06_05_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_06_05_00

theorem row_00_06_05_00 : b4RowContribution (![0, 6, 11, 11] : Fin 4 → ℕ) = 21 := by
  calc
    b4RowContribution (![0, 6, 11, 11] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_00_06_05_00) :=
      sparseRow_sound (![0, 6, 11, 11] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_00_06_05_00) valid_00_06_05_00
    _ = 21 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_06_05_00 Q := by
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
        _ = 21 := by decide
#print axioms Paper7MomentGapNumeric.row_00_06_05_00

theorem weighted_00_06_05_00 : b4RawGapContribution ![0, 6, 5, 0] = 252 := by
  calc
    b4RawGapContribution ![0, 6, 5, 0] = b4GapPatternWeight 6 5 0 * 21 :=
      b4GapContribution_from_row 0 6 5 0 21 row_00_06_05_00
    _ = 252 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_05_00

theorem row_00_06_05_01 : b4RowContribution (![0, 6, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 11, 12] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 11 + 12 = 29
    decide
  have hzsq : (∑ i, (((![0, 6, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 301 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 11^2 + 12^2 = 301
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_05_01

theorem weighted_00_06_05_01 : b4RawGapContribution ![0, 6, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 5, 1] = b4GapPatternWeight 6 5 1 * 0 :=
      b4GapContribution_from_row 0 6 5 1 0 row_00_06_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_05_01

theorem row_00_06_05_02 : b4RowContribution (![0, 6, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 11, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 11 + 13 = 30
    decide
  have hzsq : (∑ i, (((![0, 6, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 326 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 11^2 + 13^2 = 326
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_05_02

theorem weighted_00_06_05_02 : b4RawGapContribution ![0, 6, 5, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 5, 2] = b4GapPatternWeight 6 5 2 * 0 :=
      b4GapContribution_from_row 0 6 5 2 0 row_00_06_05_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_05_02

theorem row_00_06_05_03 : b4RowContribution (![0, 6, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 11, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 11 + 14 = 31
    decide
  have hzsq : (∑ i, (((![0, 6, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 353 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 11^2 + 14^2 = 353
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_05_03

theorem weighted_00_06_05_03 : b4RawGapContribution ![0, 6, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 5, 3] = b4GapPatternWeight 6 5 3 * 0 :=
      b4GapContribution_from_row 0 6 5 3 0 row_00_06_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_05_03

theorem row_00_06_05_04 : b4RowContribution (![0, 6, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 11, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 11 + 15 = 32
    decide
  have hzsq : (∑ i, (((![0, 6, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 382 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 11^2 + 15^2 = 382
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_05_04

theorem weighted_00_06_05_04 : b4RawGapContribution ![0, 6, 5, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 5, 4] = b4GapPatternWeight 6 5 4 * 0 :=
      b4GapContribution_from_row 0 6 5 4 0 row_00_06_05_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_05_04

theorem row_00_06_05_05 : b4RowContribution (![0, 6, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 11, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 11 + 16 = 33
    decide
  have hzsq : (∑ i, (((![0, 6, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 413 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 11^2 + 16^2 = 413
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_05_05

theorem weighted_00_06_05_05 : b4RawGapContribution ![0, 6, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 5, 5] = b4GapPatternWeight 6 5 5 * 0 :=
      b4GapContribution_from_row 0 6 5 5 0 row_00_06_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_05_05

theorem row_00_06_05_06 : b4RowContribution (![0, 6, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 11, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 11 + 17 = 34
    decide
  have hzsq : (∑ i, (((![0, 6, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 446 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 11^2 + 17^2 = 446
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_05_06

theorem weighted_00_06_05_06 : b4RawGapContribution ![0, 6, 5, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 5, 6] = b4GapPatternWeight 6 5 6 * 0 :=
      b4GapContribution_from_row 0 6 5 6 0 row_00_06_05_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_05_06

theorem row_00_06_05_07 : b4RowContribution (![0, 6, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 11, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 11 + 18 = 35
    decide
  have hzsq : (∑ i, (((![0, 6, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 481 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 11^2 + 18^2 = 481
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_05_07

theorem weighted_00_06_05_07 : b4RawGapContribution ![0, 6, 5, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 5, 7] = b4GapPatternWeight 6 5 7 * 0 :=
      b4GapContribution_from_row 0 6 5 7 0 row_00_06_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_05_07

theorem row_00_06_05_08 : b4RowContribution (![0, 6, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 11, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 11 + 19 = 36
    decide
  have hzsq : (∑ i, (((![0, 6, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 518 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 11^2 + 19^2 = 518
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_05_08

theorem weighted_00_06_05_08 : b4RawGapContribution ![0, 6, 5, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 5, 8] = b4GapPatternWeight 6 5 8 * 0 :=
      b4GapContribution_from_row 0 6 5 8 0 row_00_06_05_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_05_08

theorem row_00_06_05_09 : b4RowContribution (![0, 6, 11, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 6, 11, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 6 + 11 + 20 = 37
    decide
  have hzsq : (∑ i, (((![0, 6, 11, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 557 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 6^2 + 11^2 + 20^2 = 557
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_06_05_09

theorem weighted_00_06_05_09 : b4RawGapContribution ![0, 6, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 6, 5, 9] = b4GapPatternWeight 6 5 9 * 0 :=
      b4GapContribution_from_row 0 6 5 9 0 row_00_06_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_06_05_09

def dvalues_00_06_05 : Fin 10 → ℕ := ![252, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_06_05

theorem dblock_00_06_05 : b4GapPatternDBlock 0 6 5 = 252 := by
  calc
    b4GapPatternDBlock 0 6 5 = ∑ d : Fin 10, dvalues_00_06_05 d := by
      apply b4GapDBlock_of_rows 0 6 5 dvalues_00_06_05
      intro d
      fin_cases d
      · exact weighted_00_06_05_00
      · exact weighted_00_06_05_01
      · exact weighted_00_06_05_02
      · exact weighted_00_06_05_03
      · exact weighted_00_06_05_04
      · exact weighted_00_06_05_05
      · exact weighted_00_06_05_06
      · exact weighted_00_06_05_07
      · exact weighted_00_06_05_08
      · exact weighted_00_06_05_09
    _ = 252 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_06_05

end Paper7MomentGapNumeric
