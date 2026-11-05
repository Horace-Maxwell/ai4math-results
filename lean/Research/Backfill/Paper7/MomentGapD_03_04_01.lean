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

theorem row_03_04_01_00 : b4RowContribution (![3, 7, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 8, 8] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 8 + 8 = 26
    decide
  have hzsq : (∑ i, (((![3, 7, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 186 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 8^2 + 8^2 = 186
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_01_00

theorem weighted_03_04_01_00 : b4RawGapContribution ![3, 4, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 1, 0] = b4GapPatternWeight 4 1 0 * 0 :=
      b4GapContribution_from_row 3 4 1 0 0 row_03_04_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_01_00

theorem row_03_04_01_01 : b4RowContribution (![3, 7, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 8, 9] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 8 + 9 = 27
    decide
  have hzsq : (∑ i, (((![3, 7, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 203 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 8^2 + 9^2 = 203
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_01_01

theorem weighted_03_04_01_01 : b4RawGapContribution ![3, 4, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 1, 1] = b4GapPatternWeight 4 1 1 * 0 :=
      b4GapContribution_from_row 3 4 1 1 0 row_03_04_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_01_01

def layers_03_04_01_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 29, 30, 29, 26, 22, 18, 14, 10, 6, 3, 1], ![1, 4, 10, 20, 34, 52, 74, 100, 129, 159, 188, 213, 232, 244, 248, 244, 232, 213, 188]]
#print axioms Paper7MomentGapNumeric.layers_03_04_01_02

theorem cells_03_04_01_02 : QTableValid (![3, 7, 8, 10] : Fin 4 → ℕ) layers_03_04_01_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_04_01_02

theorem valid_03_04_01_02 :
    SparseRowValid (![3, 7, 8, 10] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_03_04_01_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 7, 8, 10] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 3 + 7 + 8 + 10 = 28
      decide
    have hzsq : (∑ i, (((![3, 7, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 222 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 7^2 + 8^2 + 10^2 = 222
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_04_01_02
#print axioms Paper7MomentGapNumeric.valid_03_04_01_02

def qvalues_03_04_01_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 159, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_04_01_02

theorem row_03_04_01_02 : b4RowContribution (![3, 7, 8, 10] : Fin 4 → ℕ) = 159 := by
  calc
    b4RowContribution (![3, 7, 8, 10] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_03_04_01_02) :=
      sparseRow_sound (![3, 7, 8, 10] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_03_04_01_02) valid_03_04_01_02
    _ = 159 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_04_01_02 Q := by
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
        _ = 159 := by decide
#print axioms Paper7MomentGapNumeric.row_03_04_01_02

theorem weighted_03_04_01_02 : b4RawGapContribution ![3, 4, 1, 2] = 3816 := by
  calc
    b4RawGapContribution ![3, 4, 1, 2] = b4GapPatternWeight 4 1 2 * 159 :=
      b4GapContribution_from_row 3 4 1 2 159 row_03_04_01_02
    _ = 3816 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_01_02

theorem row_03_04_01_03 : b4RowContribution (![3, 7, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 8, 11] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 8 + 11 = 29
    decide
  have hzsq : (∑ i, (((![3, 7, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 243 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 8^2 + 11^2 = 243
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_01_03

theorem weighted_03_04_01_03 : b4RawGapContribution ![3, 4, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 1, 3] = b4GapPatternWeight 4 1 3 * 0 :=
      b4GapContribution_from_row 3 4 1 3 0 row_03_04_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_01_03

theorem row_03_04_01_04 : b4RowContribution (![3, 7, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 8, 12] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 8 + 12 = 30
    decide
  have hzsq : (∑ i, (((![3, 7, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 266 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 8^2 + 12^2 = 266
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_01_04

theorem weighted_03_04_01_04 : b4RawGapContribution ![3, 4, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 1, 4] = b4GapPatternWeight 4 1 4 * 0 :=
      b4GapContribution_from_row 3 4 1 4 0 row_03_04_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_01_04

theorem row_03_04_01_05 : b4RowContribution (![3, 7, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 8, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 8 + 13 = 31
    decide
  have hzsq : (∑ i, (((![3, 7, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 291 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 8^2 + 13^2 = 291
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_01_05

theorem weighted_03_04_01_05 : b4RawGapContribution ![3, 4, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 1, 5] = b4GapPatternWeight 4 1 5 * 0 :=
      b4GapContribution_from_row 3 4 1 5 0 row_03_04_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_01_05

theorem row_03_04_01_06 : b4RowContribution (![3, 7, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 8, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 8 + 14 = 32
    decide
  have hzsq : (∑ i, (((![3, 7, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 318 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 8^2 + 14^2 = 318
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_01_06

theorem weighted_03_04_01_06 : b4RawGapContribution ![3, 4, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 1, 6] = b4GapPatternWeight 4 1 6 * 0 :=
      b4GapContribution_from_row 3 4 1 6 0 row_03_04_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_01_06

theorem row_03_04_01_07 : b4RowContribution (![3, 7, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 8, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 8 + 15 = 33
    decide
  have hzsq : (∑ i, (((![3, 7, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 347 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 8^2 + 15^2 = 347
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_01_07

theorem weighted_03_04_01_07 : b4RawGapContribution ![3, 4, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 1, 7] = b4GapPatternWeight 4 1 7 * 0 :=
      b4GapContribution_from_row 3 4 1 7 0 row_03_04_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_01_07

theorem row_03_04_01_08 : b4RowContribution (![3, 7, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 8, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 8 + 16 = 34
    decide
  have hzsq : (∑ i, (((![3, 7, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 378 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 8^2 + 16^2 = 378
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_01_08

theorem weighted_03_04_01_08 : b4RawGapContribution ![3, 4, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 1, 8] = b4GapPatternWeight 4 1 8 * 0 :=
      b4GapContribution_from_row 3 4 1 8 0 row_03_04_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_01_08

theorem row_03_04_01_09 : b4RowContribution (![3, 7, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 8, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 8 + 17 = 35
    decide
  have hzsq : (∑ i, (((![3, 7, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 411 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 8^2 + 17^2 = 411
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_01_09

theorem weighted_03_04_01_09 : b4RawGapContribution ![3, 4, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 1, 9] = b4GapPatternWeight 4 1 9 * 0 :=
      b4GapContribution_from_row 3 4 1 9 0 row_03_04_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_01_09

theorem row_03_04_01_10 : b4RowContribution (![3, 7, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 8, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 8 + 18 = 36
    decide
  have hzsq : (∑ i, (((![3, 7, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 446 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 8^2 + 18^2 = 446
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_01_10

theorem weighted_03_04_01_10 : b4RawGapContribution ![3, 4, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 1, 10] = b4GapPatternWeight 4 1 10 * 0 :=
      b4GapContribution_from_row 3 4 1 10 0 row_03_04_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_01_10

theorem row_03_04_01_11 : b4RowContribution (![3, 7, 8, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 7, 8, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 7 + 8 + 19 = 37
    decide
  have hzsq : (∑ i, (((![3, 7, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 483 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 7^2 + 8^2 + 19^2 = 483
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_04_01_11

theorem weighted_03_04_01_11 : b4RawGapContribution ![3, 4, 1, 11] = 0 := by
  calc
    b4RawGapContribution ![3, 4, 1, 11] = b4GapPatternWeight 4 1 11 * 0 :=
      b4GapContribution_from_row 3 4 1 11 0 row_03_04_01_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_04_01_11

def dvalues_03_04_01 : Fin 12 → ℕ := ![0, 0, 3816, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_04_01

theorem dblock_03_04_01 : b4GapPatternDBlock 3 4 1 = 3816 := by
  calc
    b4GapPatternDBlock 3 4 1 = ∑ d : Fin 12, dvalues_03_04_01 d := by
      apply b4GapDBlock_of_rows 3 4 1 dvalues_03_04_01
      intro d
      fin_cases d
      · exact weighted_03_04_01_00
      · exact weighted_03_04_01_01
      · exact weighted_03_04_01_02
      · exact weighted_03_04_01_03
      · exact weighted_03_04_01_04
      · exact weighted_03_04_01_05
      · exact weighted_03_04_01_06
      · exact weighted_03_04_01_07
      · exact weighted_03_04_01_08
      · exact weighted_03_04_01_09
      · exact weighted_03_04_01_10
      · exact weighted_03_04_01_11
    _ = 3816 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_04_01

end Paper7MomentGapNumeric
