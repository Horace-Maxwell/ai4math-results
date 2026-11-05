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

theorem row_01_08_00_00 : b4RowContribution (![1, 9, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 9, 9] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 9 + 9 = 28
    decide
  have hzsq : (∑ i, (((![1, 9, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 244 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 9^2 + 9^2 = 244
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_00_00

theorem weighted_01_08_00_00 : b4RawGapContribution ![1, 8, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 0, 0] = b4GapPatternWeight 8 0 0 * 0 :=
      b4GapContribution_from_row 1 8 0 0 0 row_01_08_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_00_00

theorem row_01_08_00_01 : b4RowContribution (![1, 9, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 9, 10] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 9 + 10 = 29
    decide
  have hzsq : (∑ i, (((![1, 9, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 263 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 9^2 + 10^2 = 263
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_00_01

theorem weighted_01_08_00_01 : b4RawGapContribution ![1, 8, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 0, 1] = b4GapPatternWeight 8 0 1 * 0 :=
      b4GapContribution_from_row 1 8 0 1 0 row_01_08_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_00_01

def layers_01_08_00_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 19, 17, 15, 13, 11, 9, 7, 5, 3], ![1, 4, 9, 16, 25, 36, 49, 64, 81, 100, 119, 136, 150, 160, 166, 168, 166, 160, 150]]
#print axioms Paper7MomentGapNumeric.layers_01_08_00_02

theorem cells_01_08_00_02 : QTableValid (![1, 9, 9, 11] : Fin 4 → ℕ) layers_01_08_00_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_08_00_02

theorem valid_01_08_00_02 :
    SparseRowValid (![1, 9, 9, 11] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_01_08_00_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 9, 9, 11] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 1 + 9 + 9 + 11 = 30
      decide
    have hzsq : (∑ i, (((![1, 9, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 284 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 9^2 + 9^2 + 11^2 = 284
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_08_00_02
#print axioms Paper7MomentGapNumeric.valid_01_08_00_02

def qvalues_01_08_00_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_08_00_02

theorem row_01_08_00_02 : b4RowContribution (![1, 9, 9, 11] : Fin 4 → ℕ) = 36 := by
  calc
    b4RowContribution (![1, 9, 9, 11] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_01_08_00_02) :=
      sparseRow_sound (![1, 9, 9, 11] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_01_08_00_02) valid_01_08_00_02
    _ = 36 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_08_00_02 Q := by
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
        _ = 36 := by decide
#print axioms Paper7MomentGapNumeric.row_01_08_00_02

theorem weighted_01_08_00_02 : b4RawGapContribution ![1, 8, 0, 2] = 432 := by
  calc
    b4RawGapContribution ![1, 8, 0, 2] = b4GapPatternWeight 8 0 2 * 36 :=
      b4GapContribution_from_row 1 8 0 2 36 row_01_08_00_02
    _ = 432 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_00_02

theorem row_01_08_00_03 : b4RowContribution (![1, 9, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 9, 12] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 9 + 12 = 31
    decide
  have hzsq : (∑ i, (((![1, 9, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 307 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 9^2 + 12^2 = 307
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_00_03

theorem weighted_01_08_00_03 : b4RawGapContribution ![1, 8, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 0, 3] = b4GapPatternWeight 8 0 3 * 0 :=
      b4GapContribution_from_row 1 8 0 3 0 row_01_08_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_00_03

theorem row_01_08_00_04 : b4RowContribution (![1, 9, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 9, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 9 + 13 = 32
    decide
  have hzsq : (∑ i, (((![1, 9, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 332 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 9^2 + 13^2 = 332
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_00_04

theorem weighted_01_08_00_04 : b4RawGapContribution ![1, 8, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 0, 4] = b4GapPatternWeight 8 0 4 * 0 :=
      b4GapContribution_from_row 1 8 0 4 0 row_01_08_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_00_04

theorem row_01_08_00_05 : b4RowContribution (![1, 9, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 9, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 9 + 14 = 33
    decide
  have hzsq : (∑ i, (((![1, 9, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 359 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 9^2 + 14^2 = 359
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_00_05

theorem weighted_01_08_00_05 : b4RawGapContribution ![1, 8, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 0, 5] = b4GapPatternWeight 8 0 5 * 0 :=
      b4GapContribution_from_row 1 8 0 5 0 row_01_08_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_00_05

theorem row_01_08_00_06 : b4RowContribution (![1, 9, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 9, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 9 + 15 = 34
    decide
  have hzsq : (∑ i, (((![1, 9, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 388 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 9^2 + 15^2 = 388
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_00_06

theorem weighted_01_08_00_06 : b4RawGapContribution ![1, 8, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 0, 6] = b4GapPatternWeight 8 0 6 * 0 :=
      b4GapContribution_from_row 1 8 0 6 0 row_01_08_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_00_06

theorem row_01_08_00_07 : b4RowContribution (![1, 9, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 9, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 9 + 16 = 35
    decide
  have hzsq : (∑ i, (((![1, 9, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 419 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 9^2 + 16^2 = 419
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_00_07

theorem weighted_01_08_00_07 : b4RawGapContribution ![1, 8, 0, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 0, 7] = b4GapPatternWeight 8 0 7 * 0 :=
      b4GapContribution_from_row 1 8 0 7 0 row_01_08_00_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_00_07

theorem row_01_08_00_08 : b4RowContribution (![1, 9, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 9, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 9 + 17 = 36
    decide
  have hzsq : (∑ i, (((![1, 9, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 452 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 9^2 + 17^2 = 452
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_00_08

theorem weighted_01_08_00_08 : b4RawGapContribution ![1, 8, 0, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 0, 8] = b4GapPatternWeight 8 0 8 * 0 :=
      b4GapContribution_from_row 1 8 0 8 0 row_01_08_00_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_00_08

theorem row_01_08_00_09 : b4RowContribution (![1, 9, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 9, 9, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 9 + 9 + 18 = 37
    decide
  have hzsq : (∑ i, (((![1, 9, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 487 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 9^2 + 9^2 + 18^2 = 487
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_08_00_09

theorem weighted_01_08_00_09 : b4RawGapContribution ![1, 8, 0, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 8, 0, 9] = b4GapPatternWeight 8 0 9 * 0 :=
      b4GapContribution_from_row 1 8 0 9 0 row_01_08_00_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_08_00_09

def dvalues_01_08_00 : Fin 10 → ℕ := ![0, 0, 432, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_08_00

theorem dblock_01_08_00 : b4GapPatternDBlock 1 8 0 = 432 := by
  calc
    b4GapPatternDBlock 1 8 0 = ∑ d : Fin 10, dvalues_01_08_00 d := by
      apply b4GapDBlock_of_rows 1 8 0 dvalues_01_08_00
      intro d
      fin_cases d
      · exact weighted_01_08_00_00
      · exact weighted_01_08_00_01
      · exact weighted_01_08_00_02
      · exact weighted_01_08_00_03
      · exact weighted_01_08_00_04
      · exact weighted_01_08_00_05
      · exact weighted_01_08_00_06
      · exact weighted_01_08_00_07
      · exact weighted_01_08_00_08
      · exact weighted_01_08_00_09
    _ = 432 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_08_00

end Paper7MomentGapNumeric
