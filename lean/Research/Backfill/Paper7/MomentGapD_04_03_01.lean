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

theorem row_04_03_01_00 : b4RowContribution (![4, 7, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 8, 8] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 8 + 8 = 27
    decide
  have hzsq : (∑ i, (((![4, 7, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 193 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 8^2 + 8^2 = 193
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_01_00

theorem weighted_04_03_01_00 : b4RawGapContribution ![4, 3, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 1, 0] = b4GapPatternWeight 3 1 0 * 0 :=
      b4GapContribution_from_row 4 3 1 0 0 row_04_03_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_01_00

theorem row_04_03_01_01 : b4RowContribution (![4, 7, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 8, 9] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 8 + 9 = 28
    decide
  have hzsq : (∑ i, (((![4, 7, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 210 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 8^2 + 9^2 = 210
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_01_01

theorem weighted_04_03_01_01 : b4RawGapContribution ![4, 3, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 1, 1] = b4GapPatternWeight 3 1 1 * 0 :=
      b4GapContribution_from_row 4 3 1 1 0 row_04_03_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_01_01

def layers_04_03_01_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 34, 36, 36, 34, 30, 25, 20, 15, 10, 6, 3], ![1, 4, 10, 20, 35, 55, 80, 110, 144, 180, 216, 249, 276, 295, 305, 305, 295, 276, 249]]
#print axioms Paper7MomentGapNumeric.layers_04_03_01_02

theorem cells_04_03_01_02 : QTableValid (![4, 7, 8, 10] : Fin 4 → ℕ) layers_04_03_01_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_03_01_02

theorem valid_04_03_01_02 :
    SparseRowValid (![4, 7, 8, 10] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_04_03_01_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 7, 8, 10] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 4 + 7 + 8 + 10 = 29
      decide
    have hzsq : (∑ i, (((![4, 7, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 229 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 7^2 + 8^2 + 10^2 = 229
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_03_01_02
#print axioms Paper7MomentGapNumeric.valid_04_03_01_02

def qvalues_04_03_01_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_03_01_02

theorem row_04_03_01_02 : b4RowContribution (![4, 7, 8, 10] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![4, 7, 8, 10] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_04_03_01_02) :=
      sparseRow_sound (![4, 7, 8, 10] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_04_03_01_02) valid_04_03_01_02
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_03_01_02 Q := by
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
        _ = 35 := by decide
#print axioms Paper7MomentGapNumeric.row_04_03_01_02

theorem weighted_04_03_01_02 : b4RawGapContribution ![4, 3, 1, 2] = 840 := by
  calc
    b4RawGapContribution ![4, 3, 1, 2] = b4GapPatternWeight 3 1 2 * 35 :=
      b4GapContribution_from_row 4 3 1 2 35 row_04_03_01_02
    _ = 840 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_01_02

theorem row_04_03_01_03 : b4RowContribution (![4, 7, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 8, 11] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 8 + 11 = 30
    decide
  have hzsq : (∑ i, (((![4, 7, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 250 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 8^2 + 11^2 = 250
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_01_03

theorem weighted_04_03_01_03 : b4RawGapContribution ![4, 3, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 1, 3] = b4GapPatternWeight 3 1 3 * 0 :=
      b4GapContribution_from_row 4 3 1 3 0 row_04_03_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_01_03

theorem row_04_03_01_04 : b4RowContribution (![4, 7, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 8, 12] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 8 + 12 = 31
    decide
  have hzsq : (∑ i, (((![4, 7, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 273 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 8^2 + 12^2 = 273
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_01_04

theorem weighted_04_03_01_04 : b4RawGapContribution ![4, 3, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 1, 4] = b4GapPatternWeight 3 1 4 * 0 :=
      b4GapContribution_from_row 4 3 1 4 0 row_04_03_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_01_04

theorem row_04_03_01_05 : b4RowContribution (![4, 7, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 8, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 8 + 13 = 32
    decide
  have hzsq : (∑ i, (((![4, 7, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 298 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 8^2 + 13^2 = 298
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_01_05

theorem weighted_04_03_01_05 : b4RawGapContribution ![4, 3, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 1, 5] = b4GapPatternWeight 3 1 5 * 0 :=
      b4GapContribution_from_row 4 3 1 5 0 row_04_03_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_01_05

theorem row_04_03_01_06 : b4RowContribution (![4, 7, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 8, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 8 + 14 = 33
    decide
  have hzsq : (∑ i, (((![4, 7, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 8^2 + 14^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_01_06

theorem weighted_04_03_01_06 : b4RawGapContribution ![4, 3, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 1, 6] = b4GapPatternWeight 3 1 6 * 0 :=
      b4GapContribution_from_row 4 3 1 6 0 row_04_03_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_01_06

theorem row_04_03_01_07 : b4RowContribution (![4, 7, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 8, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 8 + 15 = 34
    decide
  have hzsq : (∑ i, (((![4, 7, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 354 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 8^2 + 15^2 = 354
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_01_07

theorem weighted_04_03_01_07 : b4RawGapContribution ![4, 3, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 1, 7] = b4GapPatternWeight 3 1 7 * 0 :=
      b4GapContribution_from_row 4 3 1 7 0 row_04_03_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_01_07

theorem row_04_03_01_08 : b4RowContribution (![4, 7, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 8, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 8 + 16 = 35
    decide
  have hzsq : (∑ i, (((![4, 7, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 385 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 8^2 + 16^2 = 385
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_01_08

theorem weighted_04_03_01_08 : b4RawGapContribution ![4, 3, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 1, 8] = b4GapPatternWeight 3 1 8 * 0 :=
      b4GapContribution_from_row 4 3 1 8 0 row_04_03_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_01_08

theorem row_04_03_01_09 : b4RowContribution (![4, 7, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 8, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 8 + 17 = 36
    decide
  have hzsq : (∑ i, (((![4, 7, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 418 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 8^2 + 17^2 = 418
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_01_09

theorem weighted_04_03_01_09 : b4RawGapContribution ![4, 3, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 1, 9] = b4GapPatternWeight 3 1 9 * 0 :=
      b4GapContribution_from_row 4 3 1 9 0 row_04_03_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_01_09

theorem row_04_03_01_10 : b4RowContribution (![4, 7, 8, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 7, 8, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 7 + 8 + 18 = 37
    decide
  have hzsq : (∑ i, (((![4, 7, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 453 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 7^2 + 8^2 + 18^2 = 453
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_03_01_10

theorem weighted_04_03_01_10 : b4RawGapContribution ![4, 3, 1, 10] = 0 := by
  calc
    b4RawGapContribution ![4, 3, 1, 10] = b4GapPatternWeight 3 1 10 * 0 :=
      b4GapContribution_from_row 4 3 1 10 0 row_04_03_01_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_03_01_10

def dvalues_04_03_01 : Fin 11 → ℕ := ![0, 0, 840, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_03_01

theorem dblock_04_03_01 : b4GapPatternDBlock 4 3 1 = 840 := by
  calc
    b4GapPatternDBlock 4 3 1 = ∑ d : Fin 11, dvalues_04_03_01 d := by
      apply b4GapDBlock_of_rows 4 3 1 dvalues_04_03_01
      intro d
      fin_cases d
      · exact weighted_04_03_01_00
      · exact weighted_04_03_01_01
      · exact weighted_04_03_01_02
      · exact weighted_04_03_01_03
      · exact weighted_04_03_01_04
      · exact weighted_04_03_01_05
      · exact weighted_04_03_01_06
      · exact weighted_04_03_01_07
      · exact weighted_04_03_01_08
      · exact weighted_04_03_01_09
      · exact weighted_04_03_01_10
    _ = 840 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_03_01

end Paper7MomentGapNumeric
