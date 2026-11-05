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

def layers_05_01_03_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 27, 32, 36, 39, 40, 39, 36, 32, 27, 21, 15, 10, 6], ![1, 4, 10, 20, 35, 56, 83, 115, 151, 190, 229, 265, 295, 317, 329, 329, 317, 295, 265]]
#print axioms Paper7MomentGapNumeric.layers_05_01_03_00

theorem cells_05_01_03_00 : QTableValid (![5, 6, 9, 9] : Fin 4 → ℕ) layers_05_01_03_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_05_01_03_00

theorem valid_05_01_03_00 :
    SparseRowValid (![5, 6, 9, 9] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_05_01_03_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![5, 6, 9, 9] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 5 + 6 + 9 + 9 = 29
      decide
    have hzsq : (∑ i, (((![5, 6, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 223 := by
      rw [Fin.sum_univ_four]
      change (5 : ℤ)^2 + 6^2 + 9^2 + 9^2 = 223
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_05_01_03_00
#print axioms Paper7MomentGapNumeric.valid_05_01_03_00

def qvalues_05_01_03_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 115, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_05_01_03_00

theorem row_05_01_03_00 : b4RowContribution (![5, 6, 9, 9] : Fin 4 → ℕ) = 115 := by
  calc
    b4RowContribution (![5, 6, 9, 9] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_05_01_03_00) :=
      sparseRow_sound (![5, 6, 9, 9] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_05_01_03_00) valid_05_01_03_00
    _ = 115 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_05_01_03_00 Q := by
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
        _ = 115 := by decide
#print axioms Paper7MomentGapNumeric.row_05_01_03_00

theorem weighted_05_01_03_00 : b4RawGapContribution ![5, 1, 3, 0] = 1380 := by
  calc
    b4RawGapContribution ![5, 1, 3, 0] = b4GapPatternWeight 1 3 0 * 115 :=
      b4GapContribution_from_row 5 1 3 0 115 row_05_01_03_00
    _ = 1380 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_03_00

theorem row_05_01_03_01 : b4RowContribution (![5, 6, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 9, 10] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 9 + 10 = 30
    decide
  have hzsq : (∑ i, (((![5, 6, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 242 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 9^2 + 10^2 = 242
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_03_01

theorem weighted_05_01_03_01 : b4RawGapContribution ![5, 1, 3, 1] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 3, 1] = b4GapPatternWeight 1 3 1 * 0 :=
      b4GapContribution_from_row 5 1 3 1 0 row_05_01_03_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_03_01

theorem row_05_01_03_02 : b4RowContribution (![5, 6, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 9, 11] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 9 + 11 = 31
    decide
  have hzsq : (∑ i, (((![5, 6, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 263 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 9^2 + 11^2 = 263
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_03_02

theorem weighted_05_01_03_02 : b4RawGapContribution ![5, 1, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 3, 2] = b4GapPatternWeight 1 3 2 * 0 :=
      b4GapContribution_from_row 5 1 3 2 0 row_05_01_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_03_02

theorem row_05_01_03_03 : b4RowContribution (![5, 6, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 9, 12] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 9 + 12 = 32
    decide
  have hzsq : (∑ i, (((![5, 6, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 286 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 9^2 + 12^2 = 286
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_03_03

theorem weighted_05_01_03_03 : b4RawGapContribution ![5, 1, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 3, 3] = b4GapPatternWeight 1 3 3 * 0 :=
      b4GapContribution_from_row 5 1 3 3 0 row_05_01_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_03_03

theorem row_05_01_03_04 : b4RowContribution (![5, 6, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 9, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 9 + 13 = 33
    decide
  have hzsq : (∑ i, (((![5, 6, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 311 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 9^2 + 13^2 = 311
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_03_04

theorem weighted_05_01_03_04 : b4RawGapContribution ![5, 1, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 3, 4] = b4GapPatternWeight 1 3 4 * 0 :=
      b4GapContribution_from_row 5 1 3 4 0 row_05_01_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_03_04

theorem row_05_01_03_05 : b4RowContribution (![5, 6, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 9, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 9 + 14 = 34
    decide
  have hzsq : (∑ i, (((![5, 6, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 338 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 9^2 + 14^2 = 338
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_03_05

theorem weighted_05_01_03_05 : b4RawGapContribution ![5, 1, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 3, 5] = b4GapPatternWeight 1 3 5 * 0 :=
      b4GapContribution_from_row 5 1 3 5 0 row_05_01_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_03_05

theorem row_05_01_03_06 : b4RowContribution (![5, 6, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 9, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 9 + 15 = 35
    decide
  have hzsq : (∑ i, (((![5, 6, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 367 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 9^2 + 15^2 = 367
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_03_06

theorem weighted_05_01_03_06 : b4RawGapContribution ![5, 1, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 3, 6] = b4GapPatternWeight 1 3 6 * 0 :=
      b4GapContribution_from_row 5 1 3 6 0 row_05_01_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_03_06

theorem row_05_01_03_07 : b4RowContribution (![5, 6, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 9, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 9 + 16 = 36
    decide
  have hzsq : (∑ i, (((![5, 6, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 398 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 9^2 + 16^2 = 398
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_03_07

theorem weighted_05_01_03_07 : b4RawGapContribution ![5, 1, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 3, 7] = b4GapPatternWeight 1 3 7 * 0 :=
      b4GapContribution_from_row 5 1 3 7 0 row_05_01_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_03_07

theorem row_05_01_03_08 : b4RowContribution (![5, 6, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 9, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 9 + 17 = 37
    decide
  have hzsq : (∑ i, (((![5, 6, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 431 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 9^2 + 17^2 = 431
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_03_08

theorem weighted_05_01_03_08 : b4RawGapContribution ![5, 1, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 3, 8] = b4GapPatternWeight 1 3 8 * 0 :=
      b4GapContribution_from_row 5 1 3 8 0 row_05_01_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_03_08

def dvalues_05_01_03 : Fin 9 → ℕ := ![1380, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_01_03

theorem dblock_05_01_03 : b4GapPatternDBlock 5 1 3 = 1380 := by
  calc
    b4GapPatternDBlock 5 1 3 = ∑ d : Fin 9, dvalues_05_01_03 d := by
      apply b4GapDBlock_of_rows 5 1 3 dvalues_05_01_03
      intro d
      fin_cases d
      · exact weighted_05_01_03_00
      · exact weighted_05_01_03_01
      · exact weighted_05_01_03_02
      · exact weighted_05_01_03_03
      · exact weighted_05_01_03_04
      · exact weighted_05_01_03_05
      · exact weighted_05_01_03_06
      · exact weighted_05_01_03_07
      · exact weighted_05_01_03_08
    _ = 1380 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_01_03

end Paper7MomentGapNumeric
