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

theorem row_01_03_07_00 : b4RowContribution (![1, 4, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 11, 11] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 11 + 11 = 27
    decide
  have hzsq : (∑ i, (((![1, 4, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 259 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 11^2 + 11^2 = 259
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_07_00

theorem weighted_01_03_07_00 : b4RawGapContribution ![1, 3, 7, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 7, 0] = b4GapPatternWeight 3 7 0 * 0 :=
      b4GapContribution_from_row 1 3 7 0 0 row_01_03_07_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_07_00

def layers_01_03_07_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 9, 10, 10, 10, 10, 10, 10, 10, 9, 7, 5, 3, 1, 0, 0], ![1, 4, 9, 16, 25, 35, 45, 55, 65, 75, 85, 95, 104, 110, 112, 110, 104, 95, 85]]
#print axioms Paper7MomentGapNumeric.layers_01_03_07_01

theorem cells_01_03_07_01 : QTableValid (![1, 4, 11, 12] : Fin 4 → ℕ) layers_01_03_07_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_03_07_01

theorem valid_01_03_07_01 :
    SparseRowValid (![1, 4, 11, 12] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_03_07_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 4, 11, 12] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 1 + 4 + 11 + 12 = 28
      decide
    have hzsq : (∑ i, (((![1, 4, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 282 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 4^2 + 11^2 + 12^2 = 282
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_03_07_01
#print axioms Paper7MomentGapNumeric.valid_01_03_07_01

def qvalues_01_03_07_01 : Fin 19 → ℕ := ![0, 0, 0, 16, 0, 0, 0, 0, 0, 75, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_03_07_01

theorem row_01_03_07_01 : b4RowContribution (![1, 4, 11, 12] : Fin 4 → ℕ) = 91 := by
  calc
    b4RowContribution (![1, 4, 11, 12] : Fin 4 → ℕ) =
        sparseRowValue ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_03_07_01) :=
      sparseRow_sound (![1, 4, 11, 12] : Fin 4 → ℕ) ({3, 9} : Finset (Fin 19)) (fun _ => layers_01_03_07_01) valid_01_03_07_01
    _ = 91 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_03_07_01 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
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
        _ = 91 := by decide
#print axioms Paper7MomentGapNumeric.row_01_03_07_01

theorem weighted_01_03_07_01 : b4RawGapContribution ![1, 3, 7, 1] = 2184 := by
  calc
    b4RawGapContribution ![1, 3, 7, 1] = b4GapPatternWeight 3 7 1 * 91 :=
      b4GapContribution_from_row 1 3 7 1 91 row_01_03_07_01
    _ = 2184 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_07_01

theorem row_01_03_07_02 : b4RowContribution (![1, 4, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 11, 13] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 11 + 13 = 29
    decide
  have hzsq : (∑ i, (((![1, 4, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 307 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 11^2 + 13^2 = 307
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_07_02

theorem weighted_01_03_07_02 : b4RawGapContribution ![1, 3, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 7, 2] = b4GapPatternWeight 3 7 2 * 0 :=
      b4GapContribution_from_row 1 3 7 2 0 row_01_03_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_07_02

theorem row_01_03_07_03 : b4RowContribution (![1, 4, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 11, 14] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 11 + 14 = 30
    decide
  have hzsq : (∑ i, (((![1, 4, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 334 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 11^2 + 14^2 = 334
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_07_03

theorem weighted_01_03_07_03 : b4RawGapContribution ![1, 3, 7, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 7, 3] = b4GapPatternWeight 3 7 3 * 0 :=
      b4GapContribution_from_row 1 3 7 3 0 row_01_03_07_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_07_03

theorem row_01_03_07_04 : b4RowContribution (![1, 4, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 11, 15] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 11 + 15 = 31
    decide
  have hzsq : (∑ i, (((![1, 4, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 363 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 11^2 + 15^2 = 363
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_07_04

theorem weighted_01_03_07_04 : b4RawGapContribution ![1, 3, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 7, 4] = b4GapPatternWeight 3 7 4 * 0 :=
      b4GapContribution_from_row 1 3 7 4 0 row_01_03_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_07_04

theorem row_01_03_07_05 : b4RowContribution (![1, 4, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 11, 16] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 11 + 16 = 32
    decide
  have hzsq : (∑ i, (((![1, 4, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 394 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 11^2 + 16^2 = 394
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_07_05

theorem weighted_01_03_07_05 : b4RawGapContribution ![1, 3, 7, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 7, 5] = b4GapPatternWeight 3 7 5 * 0 :=
      b4GapContribution_from_row 1 3 7 5 0 row_01_03_07_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_07_05

theorem row_01_03_07_06 : b4RowContribution (![1, 4, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 11, 17] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 11 + 17 = 33
    decide
  have hzsq : (∑ i, (((![1, 4, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 427 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 11^2 + 17^2 = 427
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_07_06

theorem weighted_01_03_07_06 : b4RawGapContribution ![1, 3, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 7, 6] = b4GapPatternWeight 3 7 6 * 0 :=
      b4GapContribution_from_row 1 3 7 6 0 row_01_03_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_07_06

theorem row_01_03_07_07 : b4RowContribution (![1, 4, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 11, 18] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 11 + 18 = 34
    decide
  have hzsq : (∑ i, (((![1, 4, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 462 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 11^2 + 18^2 = 462
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_07_07

theorem weighted_01_03_07_07 : b4RawGapContribution ![1, 3, 7, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 7, 7] = b4GapPatternWeight 3 7 7 * 0 :=
      b4GapContribution_from_row 1 3 7 7 0 row_01_03_07_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_07_07

theorem row_01_03_07_08 : b4RowContribution (![1, 4, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 11, 19] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 11 + 19 = 35
    decide
  have hzsq : (∑ i, (((![1, 4, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 499 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 11^2 + 19^2 = 499
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_07_08

theorem weighted_01_03_07_08 : b4RawGapContribution ![1, 3, 7, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 7, 8] = b4GapPatternWeight 3 7 8 * 0 :=
      b4GapContribution_from_row 1 3 7 8 0 row_01_03_07_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_07_08

theorem row_01_03_07_09 : b4RowContribution (![1, 4, 11, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 11, 20] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 11 + 20 = 36
    decide
  have hzsq : (∑ i, (((![1, 4, 11, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 538 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 11^2 + 20^2 = 538
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_07_09

theorem weighted_01_03_07_09 : b4RawGapContribution ![1, 3, 7, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 7, 9] = b4GapPatternWeight 3 7 9 * 0 :=
      b4GapContribution_from_row 1 3 7 9 0 row_01_03_07_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_07_09

theorem row_01_03_07_10 : b4RowContribution (![1, 4, 11, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 4, 11, 21] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 4 + 11 + 21 = 37
    decide
  have hzsq : (∑ i, (((![1, 4, 11, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 579 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 4^2 + 11^2 + 21^2 = 579
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_03_07_10

theorem weighted_01_03_07_10 : b4RawGapContribution ![1, 3, 7, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 3, 7, 10] = b4GapPatternWeight 3 7 10 * 0 :=
      b4GapContribution_from_row 1 3 7 10 0 row_01_03_07_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_03_07_10

def dvalues_01_03_07 : Fin 11 → ℕ := ![0, 2184, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_03_07

theorem dblock_01_03_07 : b4GapPatternDBlock 1 3 7 = 2184 := by
  calc
    b4GapPatternDBlock 1 3 7 = ∑ d : Fin 11, dvalues_01_03_07 d := by
      apply b4GapDBlock_of_rows 1 3 7 dvalues_01_03_07
      intro d
      fin_cases d
      · exact weighted_01_03_07_00
      · exact weighted_01_03_07_01
      · exact weighted_01_03_07_02
      · exact weighted_01_03_07_03
      · exact weighted_01_03_07_04
      · exact weighted_01_03_07_05
      · exact weighted_01_03_07_06
      · exact weighted_01_03_07_07
      · exact weighted_01_03_07_08
      · exact weighted_01_03_07_09
      · exact weighted_01_03_07_10
    _ = 2184 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_03_07

end Paper7MomentGapNumeric
