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

theorem row_05_01_02_00 : b4RowContribution (![5, 6, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 8, 8] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 8 + 8 = 27
    decide
  have hzsq : (∑ i, (((![5, 6, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 189 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 8^2 + 8^2 = 189
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_02_00

theorem weighted_05_01_02_00 : b4RawGapContribution ![5, 1, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 2, 0] = b4GapPatternWeight 1 2 0 * 0 :=
      b4GapContribution_from_row 5 1 2 0 0 row_05_01_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_02_00

theorem row_05_01_02_01 : b4RowContribution (![5, 6, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 8, 9] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 8 + 9 = 28
    decide
  have hzsq : (∑ i, (((![5, 6, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 206 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 8^2 + 9^2 = 206
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_02_01

theorem weighted_05_01_02_01 : b4RawGapContribution ![5, 1, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 2, 1] = b4GapPatternWeight 1 2 1 * 0 :=
      b4GapContribution_from_row 5 1 2 1 0 row_05_01_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_02_01

def layers_05_01_02_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 27, 32, 36, 38, 38, 36, 32, 27, 21, 15, 10, 6, 3], ![1, 4, 10, 20, 35, 56, 83, 115, 151, 189, 227, 262, 291, 312, 323, 323, 312, 291, 262]]
#print axioms Paper7MomentGapNumeric.layers_05_01_02_02

theorem cells_05_01_02_02 : QTableValid (![5, 6, 8, 10] : Fin 4 → ℕ) layers_05_01_02_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_05_01_02_02

theorem valid_05_01_02_02 :
    SparseRowValid (![5, 6, 8, 10] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_05_01_02_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![5, 6, 8, 10] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 5 + 6 + 8 + 10 = 29
      decide
    have hzsq : (∑ i, (((![5, 6, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 225 := by
      rw [Fin.sum_univ_four]
      change (5 : ℤ)^2 + 6^2 + 8^2 + 10^2 = 225
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_05_01_02_02
#print axioms Paper7MomentGapNumeric.valid_05_01_02_02

def qvalues_05_01_02_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_05_01_02_02

theorem row_05_01_02_02 : b4RowContribution (![5, 6, 8, 10] : Fin 4 → ℕ) = 83 := by
  calc
    b4RowContribution (![5, 6, 8, 10] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_05_01_02_02) :=
      sparseRow_sound (![5, 6, 8, 10] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_05_01_02_02) valid_05_01_02_02
    _ = 83 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_05_01_02_02 Q := by
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
        _ = 83 := by decide
#print axioms Paper7MomentGapNumeric.row_05_01_02_02

theorem weighted_05_01_02_02 : b4RawGapContribution ![5, 1, 2, 2] = 1992 := by
  calc
    b4RawGapContribution ![5, 1, 2, 2] = b4GapPatternWeight 1 2 2 * 83 :=
      b4GapContribution_from_row 5 1 2 2 83 row_05_01_02_02
    _ = 1992 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_02_02

theorem row_05_01_02_03 : b4RowContribution (![5, 6, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 8, 11] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 8 + 11 = 30
    decide
  have hzsq : (∑ i, (((![5, 6, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 246 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 8^2 + 11^2 = 246
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_02_03

theorem weighted_05_01_02_03 : b4RawGapContribution ![5, 1, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 2, 3] = b4GapPatternWeight 1 2 3 * 0 :=
      b4GapContribution_from_row 5 1 2 3 0 row_05_01_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_02_03

theorem row_05_01_02_04 : b4RowContribution (![5, 6, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 8, 12] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 8 + 12 = 31
    decide
  have hzsq : (∑ i, (((![5, 6, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 269 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 8^2 + 12^2 = 269
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_02_04

theorem weighted_05_01_02_04 : b4RawGapContribution ![5, 1, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 2, 4] = b4GapPatternWeight 1 2 4 * 0 :=
      b4GapContribution_from_row 5 1 2 4 0 row_05_01_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_02_04

theorem row_05_01_02_05 : b4RowContribution (![5, 6, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 8, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 8 + 13 = 32
    decide
  have hzsq : (∑ i, (((![5, 6, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 294 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 8^2 + 13^2 = 294
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_02_05

theorem weighted_05_01_02_05 : b4RawGapContribution ![5, 1, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 2, 5] = b4GapPatternWeight 1 2 5 * 0 :=
      b4GapContribution_from_row 5 1 2 5 0 row_05_01_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_02_05

theorem row_05_01_02_06 : b4RowContribution (![5, 6, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 8, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 8 + 14 = 33
    decide
  have hzsq : (∑ i, (((![5, 6, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 321 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 8^2 + 14^2 = 321
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_02_06

theorem weighted_05_01_02_06 : b4RawGapContribution ![5, 1, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 2, 6] = b4GapPatternWeight 1 2 6 * 0 :=
      b4GapContribution_from_row 5 1 2 6 0 row_05_01_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_02_06

theorem row_05_01_02_07 : b4RowContribution (![5, 6, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 8, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 8 + 15 = 34
    decide
  have hzsq : (∑ i, (((![5, 6, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 350 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 8^2 + 15^2 = 350
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_02_07

theorem weighted_05_01_02_07 : b4RawGapContribution ![5, 1, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 2, 7] = b4GapPatternWeight 1 2 7 * 0 :=
      b4GapContribution_from_row 5 1 2 7 0 row_05_01_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_02_07

theorem row_05_01_02_08 : b4RowContribution (![5, 6, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 8, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 8 + 16 = 35
    decide
  have hzsq : (∑ i, (((![5, 6, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 381 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 8^2 + 16^2 = 381
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_02_08

theorem weighted_05_01_02_08 : b4RawGapContribution ![5, 1, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 2, 8] = b4GapPatternWeight 1 2 8 * 0 :=
      b4GapContribution_from_row 5 1 2 8 0 row_05_01_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_02_08

theorem row_05_01_02_09 : b4RowContribution (![5, 6, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 8, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 8 + 17 = 36
    decide
  have hzsq : (∑ i, (((![5, 6, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 414 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 8^2 + 17^2 = 414
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_02_09

theorem weighted_05_01_02_09 : b4RawGapContribution ![5, 1, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 2, 9] = b4GapPatternWeight 1 2 9 * 0 :=
      b4GapContribution_from_row 5 1 2 9 0 row_05_01_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_02_09

theorem row_05_01_02_10 : b4RowContribution (![5, 6, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 8, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 8 + 18 = 37
    decide
  have hzsq : (∑ i, (((![5, 6, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 449 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 8^2 + 18^2 = 449
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_02_10

theorem weighted_05_01_02_10 : b4RawGapContribution ![5, 1, 2, 10] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 2, 10] = b4GapPatternWeight 1 2 10 * 0 :=
      b4GapContribution_from_row 5 1 2 10 0 row_05_01_02_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_02_10

def dvalues_05_01_02 : Fin 11 → ℕ := ![0, 0, 1992, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_01_02

theorem dblock_05_01_02 : b4GapPatternDBlock 5 1 2 = 1992 := by
  calc
    b4GapPatternDBlock 5 1 2 = ∑ d : Fin 11, dvalues_05_01_02 d := by
      apply b4GapDBlock_of_rows 5 1 2 dvalues_05_01_02
      intro d
      fin_cases d
      · exact weighted_05_01_02_00
      · exact weighted_05_01_02_01
      · exact weighted_05_01_02_02
      · exact weighted_05_01_02_03
      · exact weighted_05_01_02_04
      · exact weighted_05_01_02_05
      · exact weighted_05_01_02_06
      · exact weighted_05_01_02_07
      · exact weighted_05_01_02_08
      · exact weighted_05_01_02_09
      · exact weighted_05_01_02_10
    _ = 1992 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_01_02

end Paper7MomentGapNumeric
