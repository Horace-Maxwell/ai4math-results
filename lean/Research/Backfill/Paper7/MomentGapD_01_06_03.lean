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

theorem row_01_06_03_00 : b4RowContribution (![1, 7, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 10, 10] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 10 + 10 = 28
    decide
  have hzsq : (∑ i, (((![1, 7, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 250 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 10^2 + 10^2 = 250
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_03_00

theorem weighted_01_06_03_00 : b4RawGapContribution ![1, 6, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 3, 0] = b4GapPatternWeight 6 3 0 * 0 :=
      b4GapContribution_from_row 1 6 3 0 0 row_01_06_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_03_00

def layers_01_06_03_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 16, 16, 16, 15, 13, 11, 9, 7, 5, 3, 1], ![1, 4, 9, 16, 25, 36, 49, 64, 80, 96, 112, 127, 139, 147, 151, 151, 147, 139, 127]]
#print axioms Paper7MomentGapNumeric.layers_01_06_03_01

theorem cells_01_06_03_01 : QTableValid (![1, 7, 10, 11] : Fin 4 → ℕ) layers_01_06_03_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_06_03_01

theorem valid_01_06_03_01 :
    SparseRowValid (![1, 7, 10, 11] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_06_03_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 7, 10, 11] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 1 + 7 + 10 + 11 = 29
      decide
    have hzsq : (∑ i, (((![1, 7, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 271 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 7^2 + 10^2 + 11^2 = 271
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_06_03_01
#print axioms Paper7MomentGapNumeric.valid_01_06_03_01

def qvalues_01_06_03_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_06_03_01

theorem row_01_06_03_01 : b4RowContribution (![1, 7, 10, 11] : Fin 4 → ℕ) = 64 := by
  calc
    b4RowContribution (![1, 7, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_01_06_03_01) :=
      sparseRow_sound (![1, 7, 10, 11] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_06_03_01) valid_01_06_03_01
    _ = 64 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_06_03_01 Q := by
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
        _ = 64 := by decide
#print axioms Paper7MomentGapNumeric.row_01_06_03_01

theorem weighted_01_06_03_01 : b4RawGapContribution ![1, 6, 3, 1] = 1536 := by
  calc
    b4RawGapContribution ![1, 6, 3, 1] = b4GapPatternWeight 6 3 1 * 64 :=
      b4GapContribution_from_row 1 6 3 1 64 row_01_06_03_01
    _ = 1536 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_03_01

theorem row_01_06_03_02 : b4RowContribution (![1, 7, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 10, 12] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 10 + 12 = 30
    decide
  have hzsq : (∑ i, (((![1, 7, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 294 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 10^2 + 12^2 = 294
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_03_02

theorem weighted_01_06_03_02 : b4RawGapContribution ![1, 6, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 3, 2] = b4GapPatternWeight 6 3 2 * 0 :=
      b4GapContribution_from_row 1 6 3 2 0 row_01_06_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_03_02

theorem row_01_06_03_03 : b4RowContribution (![1, 7, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 10, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 10 + 13 = 31
    decide
  have hzsq : (∑ i, (((![1, 7, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 319 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 10^2 + 13^2 = 319
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_03_03

theorem weighted_01_06_03_03 : b4RawGapContribution ![1, 6, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 3, 3] = b4GapPatternWeight 6 3 3 * 0 :=
      b4GapContribution_from_row 1 6 3 3 0 row_01_06_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_03_03

theorem row_01_06_03_04 : b4RowContribution (![1, 7, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 10, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 10 + 14 = 32
    decide
  have hzsq : (∑ i, (((![1, 7, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 346 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 10^2 + 14^2 = 346
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_03_04

theorem weighted_01_06_03_04 : b4RawGapContribution ![1, 6, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 3, 4] = b4GapPatternWeight 6 3 4 * 0 :=
      b4GapContribution_from_row 1 6 3 4 0 row_01_06_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_03_04

theorem row_01_06_03_05 : b4RowContribution (![1, 7, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 10, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 10 + 15 = 33
    decide
  have hzsq : (∑ i, (((![1, 7, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 375 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 10^2 + 15^2 = 375
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_03_05

theorem weighted_01_06_03_05 : b4RawGapContribution ![1, 6, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 3, 5] = b4GapPatternWeight 6 3 5 * 0 :=
      b4GapContribution_from_row 1 6 3 5 0 row_01_06_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_03_05

theorem row_01_06_03_06 : b4RowContribution (![1, 7, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 10, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 10 + 16 = 34
    decide
  have hzsq : (∑ i, (((![1, 7, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 406 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 10^2 + 16^2 = 406
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_03_06

theorem weighted_01_06_03_06 : b4RawGapContribution ![1, 6, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 3, 6] = b4GapPatternWeight 6 3 6 * 0 :=
      b4GapContribution_from_row 1 6 3 6 0 row_01_06_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_03_06

theorem row_01_06_03_07 : b4RowContribution (![1, 7, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 10, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 10 + 17 = 35
    decide
  have hzsq : (∑ i, (((![1, 7, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 439 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 10^2 + 17^2 = 439
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_03_07

theorem weighted_01_06_03_07 : b4RawGapContribution ![1, 6, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 3, 7] = b4GapPatternWeight 6 3 7 * 0 :=
      b4GapContribution_from_row 1 6 3 7 0 row_01_06_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_03_07

theorem row_01_06_03_08 : b4RowContribution (![1, 7, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 10, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 10 + 18 = 36
    decide
  have hzsq : (∑ i, (((![1, 7, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 474 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 10^2 + 18^2 = 474
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_03_08

theorem weighted_01_06_03_08 : b4RawGapContribution ![1, 6, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 3, 8] = b4GapPatternWeight 6 3 8 * 0 :=
      b4GapContribution_from_row 1 6 3 8 0 row_01_06_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_03_08

theorem row_01_06_03_09 : b4RowContribution (![1, 7, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 7, 10, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 7 + 10 + 19 = 37
    decide
  have hzsq : (∑ i, (((![1, 7, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 511 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 7^2 + 10^2 + 19^2 = 511
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_06_03_09

theorem weighted_01_06_03_09 : b4RawGapContribution ![1, 6, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 6, 3, 9] = b4GapPatternWeight 6 3 9 * 0 :=
      b4GapContribution_from_row 1 6 3 9 0 row_01_06_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_06_03_09

def dvalues_01_06_03 : Fin 10 → ℕ := ![0, 1536, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_06_03

theorem dblock_01_06_03 : b4GapPatternDBlock 1 6 3 = 1536 := by
  calc
    b4GapPatternDBlock 1 6 3 = ∑ d : Fin 10, dvalues_01_06_03 d := by
      apply b4GapDBlock_of_rows 1 6 3 dvalues_01_06_03
      intro d
      fin_cases d
      · exact weighted_01_06_03_00
      · exact weighted_01_06_03_01
      · exact weighted_01_06_03_02
      · exact weighted_01_06_03_03
      · exact weighted_01_06_03_04
      · exact weighted_01_06_03_05
      · exact weighted_01_06_03_06
      · exact weighted_01_06_03_07
      · exact weighted_01_06_03_08
      · exact weighted_01_06_03_09
    _ = 1536 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_06_03

end Paper7MomentGapNumeric
