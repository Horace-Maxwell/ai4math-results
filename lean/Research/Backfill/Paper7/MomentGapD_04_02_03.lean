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

theorem row_04_02_03_00 : b4RowContribution (![4, 6, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 9, 9] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 9 + 9 = 28
    decide
  have hzsq : (∑ i, (((![4, 6, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 214 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 9^2 + 9^2 = 214
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_03_00

theorem weighted_04_02_03_00 : b4RawGapContribution ![4, 2, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 3, 0] = b4GapPatternWeight 2 3 0 * 0 :=
      b4GapContribution_from_row 4 2 3 0 0 row_04_02_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_03_00

def layers_04_02_03_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 29, 32, 34, 34, 32, 29, 25, 20, 15, 10, 6, 3], ![1, 4, 10, 20, 35, 55, 80, 109, 141, 175, 209, 240, 266, 285, 295, 295, 285, 266, 240]]
#print axioms Paper7MomentGapNumeric.layers_04_02_03_01

theorem cells_04_02_03_01 : QTableValid (![4, 6, 9, 10] : Fin 4 → ℕ) layers_04_02_03_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_02_03_01

theorem valid_04_02_03_01 :
    SparseRowValid (![4, 6, 9, 10] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_04_02_03_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 6, 9, 10] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 4 + 6 + 9 + 10 = 29
      decide
    have hzsq : (∑ i, (((![4, 6, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 233 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 6^2 + 9^2 + 10^2 = 233
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_02_03_01
#print axioms Paper7MomentGapNumeric.valid_04_02_03_01

def qvalues_04_02_03_01 : Fin 19 → ℕ := ![0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_02_03_01

theorem row_04_02_03_01 : b4RowContribution (![4, 6, 9, 10] : Fin 4 → ℕ) = 10 := by
  calc
    b4RowContribution (![4, 6, 9, 10] : Fin 4 → ℕ) =
        sparseRowValue ({2} : Finset (Fin 19)) (fun _ => layers_04_02_03_01) :=
      sparseRow_sound (![4, 6, 9, 10] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_04_02_03_01) valid_04_02_03_01
    _ = 10 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_02_03_01 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 10 := by decide
#print axioms Paper7MomentGapNumeric.row_04_02_03_01

theorem weighted_04_02_03_01 : b4RawGapContribution ![4, 2, 3, 1] = 240 := by
  calc
    b4RawGapContribution ![4, 2, 3, 1] = b4GapPatternWeight 2 3 1 * 10 :=
      b4GapContribution_from_row 4 2 3 1 10 row_04_02_03_01
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_03_01

theorem row_04_02_03_02 : b4RowContribution (![4, 6, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 9, 11] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 9 + 11 = 30
    decide
  have hzsq : (∑ i, (((![4, 6, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 254 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 9^2 + 11^2 = 254
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_03_02

theorem weighted_04_02_03_02 : b4RawGapContribution ![4, 2, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 3, 2] = b4GapPatternWeight 2 3 2 * 0 :=
      b4GapContribution_from_row 4 2 3 2 0 row_04_02_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_03_02

def layers_04_02_03_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 29, 32, 34, 34, 32, 29, 25, 20, 15, 10, 6, 3], ![1, 4, 10, 20, 35, 55, 80, 109, 141, 175, 209, 241, 270, 294, 311, 320, 320, 311, 294]]
#print axioms Paper7MomentGapNumeric.layers_04_02_03_03

theorem cells_04_02_03_03 : QTableValid (![4, 6, 9, 12] : Fin 4 → ℕ) layers_04_02_03_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_02_03_03

theorem valid_04_02_03_03 :
    SparseRowValid (![4, 6, 9, 12] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_04_02_03_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 6, 9, 12] : Fin 4 → ℕ) i) = 31 := by
      rw [Fin.sum_univ_four]
      change 4 + 6 + 9 + 12 = 31
      decide
    have hzsq : (∑ i, (((![4, 6, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 277 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 6^2 + 9^2 + 12^2 = 277
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_02_03_03
#print axioms Paper7MomentGapNumeric.valid_04_02_03_03

def qvalues_04_02_03_03 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_02_03_03

theorem row_04_02_03_03 : b4RowContribution (![4, 6, 9, 12] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![4, 6, 9, 12] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_04_02_03_03) :=
      sparseRow_sound (![4, 6, 9, 12] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_04_02_03_03) valid_04_02_03_03
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_02_03_03 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 4 := by decide
#print axioms Paper7MomentGapNumeric.row_04_02_03_03

theorem weighted_04_02_03_03 : b4RawGapContribution ![4, 2, 3, 3] = 96 := by
  calc
    b4RawGapContribution ![4, 2, 3, 3] = b4GapPatternWeight 2 3 3 * 4 :=
      b4GapContribution_from_row 4 2 3 3 4 row_04_02_03_03
    _ = 96 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_03_03

theorem row_04_02_03_04 : b4RowContribution (![4, 6, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 9, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 9 + 13 = 32
    decide
  have hzsq : (∑ i, (((![4, 6, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 302 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 9^2 + 13^2 = 302
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_03_04

theorem weighted_04_02_03_04 : b4RawGapContribution ![4, 2, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 3, 4] = b4GapPatternWeight 2 3 4 * 0 :=
      b4GapContribution_from_row 4 2 3 4 0 row_04_02_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_03_04

theorem row_04_02_03_05 : b4RowContribution (![4, 6, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 9, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 9 + 14 = 33
    decide
  have hzsq : (∑ i, (((![4, 6, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 329 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 9^2 + 14^2 = 329
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_03_05

theorem weighted_04_02_03_05 : b4RawGapContribution ![4, 2, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 3, 5] = b4GapPatternWeight 2 3 5 * 0 :=
      b4GapContribution_from_row 4 2 3 5 0 row_04_02_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_03_05

theorem row_04_02_03_06 : b4RowContribution (![4, 6, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 9, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 9 + 15 = 34
    decide
  have hzsq : (∑ i, (((![4, 6, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 358 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 9^2 + 15^2 = 358
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_03_06

theorem weighted_04_02_03_06 : b4RawGapContribution ![4, 2, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 3, 6] = b4GapPatternWeight 2 3 6 * 0 :=
      b4GapContribution_from_row 4 2 3 6 0 row_04_02_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_03_06

theorem row_04_02_03_07 : b4RowContribution (![4, 6, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 9, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 9 + 16 = 35
    decide
  have hzsq : (∑ i, (((![4, 6, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 389 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 9^2 + 16^2 = 389
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_03_07

theorem weighted_04_02_03_07 : b4RawGapContribution ![4, 2, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 3, 7] = b4GapPatternWeight 2 3 7 * 0 :=
      b4GapContribution_from_row 4 2 3 7 0 row_04_02_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_03_07

theorem row_04_02_03_08 : b4RowContribution (![4, 6, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 9, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 9 + 17 = 36
    decide
  have hzsq : (∑ i, (((![4, 6, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 422 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 9^2 + 17^2 = 422
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_03_08

theorem weighted_04_02_03_08 : b4RawGapContribution ![4, 2, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 3, 8] = b4GapPatternWeight 2 3 8 * 0 :=
      b4GapContribution_from_row 4 2 3 8 0 row_04_02_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_03_08

theorem row_04_02_03_09 : b4RowContribution (![4, 6, 9, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 6, 9, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 6 + 9 + 18 = 37
    decide
  have hzsq : (∑ i, (((![4, 6, 9, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 457 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 6^2 + 9^2 + 18^2 = 457
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_02_03_09

theorem weighted_04_02_03_09 : b4RawGapContribution ![4, 2, 3, 9] = 0 := by
  calc
    b4RawGapContribution ![4, 2, 3, 9] = b4GapPatternWeight 2 3 9 * 0 :=
      b4GapContribution_from_row 4 2 3 9 0 row_04_02_03_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_02_03_09

def dvalues_04_02_03 : Fin 10 → ℕ := ![0, 240, 0, 96, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_02_03

theorem dblock_04_02_03 : b4GapPatternDBlock 4 2 3 = 336 := by
  calc
    b4GapPatternDBlock 4 2 3 = ∑ d : Fin 10, dvalues_04_02_03 d := by
      apply b4GapDBlock_of_rows 4 2 3 dvalues_04_02_03
      intro d
      fin_cases d
      · exact weighted_04_02_03_00
      · exact weighted_04_02_03_01
      · exact weighted_04_02_03_02
      · exact weighted_04_02_03_03
      · exact weighted_04_02_03_04
      · exact weighted_04_02_03_05
      · exact weighted_04_02_03_06
      · exact weighted_04_02_03_07
      · exact weighted_04_02_03_08
      · exact weighted_04_02_03_09
    _ = 336 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_02_03

end Paper7MomentGapNumeric
