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

theorem row_03_04_02_00 : b4RowContribution (![3, 7, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 9, 9] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 9 + 9 = 28
    decide
  have hzsq : (∑ i, (((![3, 7, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 220 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 9^2 + 9^2 = 220
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_02_00

theorem weighted_03_04_02_00 : b4RawGapContribution ![3, 4, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 2, 0] = b4GapPatternWeight 4 2 0 * 0 :=
      b4GapContribution_from_row 3 4 2 0 0 row_03_04_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_02_00

theorem row_03_04_02_01 : b4RowContribution (![3, 7, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 9, 10] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 9 + 10 = 29
    decide
  have hzsq : (∑ i, (((![3, 7, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 239 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 9^2 + 10^2 = 239
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_02_01

theorem weighted_03_04_02_01 : b4RawGapContribution ![3, 4, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 2, 1] = b4GapPatternWeight 4 2 1 * 0 :=
      b4GapContribution_from_row 3 4 2 1 0 row_03_04_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_02_01

theorem row_03_04_02_02 : b4RowContribution (![3, 7, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 9, 11] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 9 + 11 = 30
    decide
  have hzsq : (∑ i, (((![3, 7, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 260 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 9^2 + 11^2 = 260
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_02_02

theorem weighted_03_04_02_02 : b4RawGapContribution ![3, 4, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 2, 2] = b4GapPatternWeight 4 2 2 * 0 :=
      b4GapContribution_from_row 3 4 2 2 0 row_03_04_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_02_02

def layers_03_04_02_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 29, 31, 31, 29, 26, 22, 18, 14, 10, 6, 3], ![1, 4, 10, 20, 34, 52, 74, 100, 129, 160, 191, 220, 246, 267, 282, 290, 290, 282, 267]]
#print axioms Paper7MomentGapNumeric.layers_03_04_02_03

theorem cells_03_04_02_03 : QTableValid (![3, 7, 9, 12] : Fin 4 → ℕ) layers_03_04_02_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_04_02_03

theorem valid_03_04_02_03 :
    SparseRowValid (![3, 7, 9, 12] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_03_04_02_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 7, 9, 12] : Fin 4 → ℕ) i) = 31 := by
      rw [Fin.sum_univ_four]
      change 3 + 7 + 9 + 12 = 31
      decide
    have hzsq : (∑ i, (((![3, 7, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 283 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 7^2 + 9^2 + 12^2 = 283
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_04_02_03
#print axioms Paper7MomentGapNumeric.valid_03_04_02_03

def qvalues_03_04_02_03 : Fin 19 → ℕ := ![0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_04_02_03

theorem row_03_04_02_03 : b4RowContribution (![3, 7, 9, 12] : Fin 4 → ℕ) = 34 := by
  calc
    b4RowContribution (![3, 7, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_03_04_02_03) :=
      sparseRow_sound (![3, 7, 9, 12] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_03_04_02_03) valid_03_04_02_03
    _ = 34 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_04_02_03 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 34 := by decide
#print axioms Paper7MomentGapNumeric.row_03_04_02_03

theorem weighted_03_04_02_03 : b4RawGapContribution ![3, 4, 2, 3] = 816 := by
  calc
    b4RawGapContribution ![3, 4, 2, 3] = b4GapPatternWeight 4 2 3 * 34 :=
      b4GapContribution_from_row 3 4 2 3 34 row_03_04_02_03
    _ = 816 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_02_03

theorem row_03_04_02_04 : b4RowContribution (![3, 7, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 9, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 9 + 13 = 32
    decide
  have hzsq : (∑ i, (((![3, 7, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 308 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 9^2 + 13^2 = 308
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_02_04

theorem weighted_03_04_02_04 : b4RawGapContribution ![3, 4, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 2, 4] = b4GapPatternWeight 4 2 4 * 0 :=
      b4GapContribution_from_row 3 4 2 4 0 row_03_04_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_02_04

theorem row_03_04_02_05 : b4RowContribution (![3, 7, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 9, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 9 + 14 = 33
    decide
  have hzsq : (∑ i, (((![3, 7, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 335 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 9^2 + 14^2 = 335
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_02_05

theorem weighted_03_04_02_05 : b4RawGapContribution ![3, 4, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 2, 5] = b4GapPatternWeight 4 2 5 * 0 :=
      b4GapContribution_from_row 3 4 2 5 0 row_03_04_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_02_05

theorem row_03_04_02_06 : b4RowContribution (![3, 7, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 9, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 9 + 15 = 34
    decide
  have hzsq : (∑ i, (((![3, 7, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 364 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 9^2 + 15^2 = 364
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_02_06

theorem weighted_03_04_02_06 : b4RawGapContribution ![3, 4, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 2, 6] = b4GapPatternWeight 4 2 6 * 0 :=
      b4GapContribution_from_row 3 4 2 6 0 row_03_04_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_02_06

theorem row_03_04_02_07 : b4RowContribution (![3, 7, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 9, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 9 + 16 = 35
    decide
  have hzsq : (∑ i, (((![3, 7, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 395 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 9^2 + 16^2 = 395
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_02_07

theorem weighted_03_04_02_07 : b4RawGapContribution ![3, 4, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 2, 7] = b4GapPatternWeight 4 2 7 * 0 :=
      b4GapContribution_from_row 3 4 2 7 0 row_03_04_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_02_07

theorem row_03_04_02_08 : b4RowContribution (![3, 7, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 9, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 9 + 17 = 36
    decide
  have hzsq : (∑ i, (((![3, 7, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 428 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 9^2 + 17^2 = 428
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_02_08

theorem weighted_03_04_02_08 : b4RawGapContribution ![3, 4, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 2, 8] = b4GapPatternWeight 4 2 8 * 0 :=
      b4GapContribution_from_row 3 4 2 8 0 row_03_04_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_02_08

theorem row_03_04_02_09 : b4RowContribution (![3, 7, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 9, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 9 + 18 = 37
    decide
  have hzsq : (∑ i, (((![3, 7, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 463 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 9^2 + 18^2 = 463
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_02_09

theorem weighted_03_04_02_09 : b4RawGapContribution ![3, 4, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 2, 9] = b4GapPatternWeight 4 2 9 * 0 :=
      b4GapContribution_from_row 3 4 2 9 0 row_03_04_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_02_09

def dvalues_03_04_02 : Fin 10 → ℕ := ![0, 0, 0, 816, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_04_02

theorem dblock_03_04_02 : b4GapPatternDBlock 3 4 2 = 816 := by
  calc
    b4GapPatternDBlock 3 4 2 = ∑ d : Fin 10, dvalues_03_04_02 d := by
      apply b4GapDBlock_of_rows 3 4 2 dvalues_03_04_02
      intro d
      fin_cases d
      · exact weighted_03_04_02_00
      · exact weighted_03_04_02_01
      · exact weighted_03_04_02_02
      · exact weighted_03_04_02_03
      · exact weighted_03_04_02_04
      · exact weighted_03_04_02_05
      · exact weighted_03_04_02_06
      · exact weighted_03_04_02_07
      · exact weighted_03_04_02_08
      · exact weighted_03_04_02_09
    _ = 816 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_04_02

end Paper7MomentGapNumeric
