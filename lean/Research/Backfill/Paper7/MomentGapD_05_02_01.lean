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

theorem row_05_02_01_00 : b4RowContribution (![5, 7, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 8, 8] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 8 + 8 = 28
    decide
  have hzsq : (∑ i, (((![5, 7, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 202 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 8^2 + 8^2 = 202
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_01_00

theorem weighted_05_02_01_00 : b4RawGapContribution ![5, 2, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 1, 0] = b4GapPatternWeight 2 1 0 * 0 :=
      b4GapContribution_from_row 5 2 1 0 0 row_05_02_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_01_00

theorem row_05_02_01_01 : b4RowContribution (![5, 7, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 8, 9] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 8 + 9 = 29
    decide
  have hzsq : (∑ i, (((![5, 7, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 219 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 8^2 + 9^2 = 219
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_01_01

theorem weighted_05_02_01_01 : b4RawGapContribution ![5, 2, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 1, 1] = b4GapPatternWeight 2 1 1 * 0 :=
      b4GapContribution_from_row 5 2 1 1 0 row_05_02_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_01_01

theorem row_05_02_01_02 : b4RowContribution (![5, 7, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 8, 10] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 8 + 10 = 30
    decide
  have hzsq : (∑ i, (((![5, 7, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 238 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 8^2 + 10^2 = 238
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_01_02

theorem weighted_05_02_01_02 : b4RawGapContribution ![5, 2, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 1, 2] = b4GapPatternWeight 2 1 2 * 0 :=
      b4GapContribution_from_row 5 2 1 2 0 row_05_02_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_01_02

theorem row_05_02_01_03 : b4RowContribution (![5, 7, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 8, 11] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 8 + 11 = 31
    decide
  have hzsq : (∑ i, (((![5, 7, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 259 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 8^2 + 11^2 = 259
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_01_03

theorem weighted_05_02_01_03 : b4RawGapContribution ![5, 2, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 1, 3] = b4GapPatternWeight 2 1 3 * 0 :=
      b4GapContribution_from_row 5 2 1 3 0 row_05_02_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_01_03

def layers_05_02_01_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 27, 33, 38, 41, 42, 41, 38, 33, 27, 21, 15, 10, 6], ![1, 4, 10, 20, 35, 56, 83, 116, 154, 195, 237, 278, 316, 348, 372, 387, 392, 387, 372]]
#print axioms Paper7MomentGapNumeric.layers_05_02_01_04

theorem cells_05_02_01_04 : QTableValid (![5, 7, 8, 12] : Fin 4 → ℕ) layers_05_02_01_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_05_02_01_04

theorem valid_05_02_01_04 :
    SparseRowValid (![5, 7, 8, 12] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_05_02_01_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![5, 7, 8, 12] : Fin 4 → ℕ) i) = 32 := by
      rw [Fin.sum_univ_four]
      change 5 + 7 + 8 + 12 = 32
      decide
    have hzsq : (∑ i, (((![5, 7, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 282 := by
      rw [Fin.sum_univ_four]
      change (5 : ℤ)^2 + 7^2 + 8^2 + 12^2 = 282
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_05_02_01_04
#print axioms Paper7MomentGapNumeric.valid_05_02_01_04

def qvalues_05_02_01_04 : Fin 19 → ℕ := ![0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_05_02_01_04

theorem row_05_02_01_04 : b4RowContribution (![5, 7, 8, 12] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![5, 7, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_05_02_01_04) :=
      sparseRow_sound (![5, 7, 8, 12] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_05_02_01_04) valid_05_02_01_04
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_05_02_01_04 Q := by
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
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_05_02_01_04

theorem weighted_05_02_01_04 : b4RawGapContribution ![5, 2, 1, 4] = 480 := by
  calc
    b4RawGapContribution ![5, 2, 1, 4] = b4GapPatternWeight 2 1 4 * 20 :=
      b4GapContribution_from_row 5 2 1 4 20 row_05_02_01_04
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_01_04

theorem row_05_02_01_05 : b4RowContribution (![5, 7, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 8, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 8 + 13 = 33
    decide
  have hzsq : (∑ i, (((![5, 7, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 307 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 8^2 + 13^2 = 307
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_01_05

theorem weighted_05_02_01_05 : b4RawGapContribution ![5, 2, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 1, 5] = b4GapPatternWeight 2 1 5 * 0 :=
      b4GapContribution_from_row 5 2 1 5 0 row_05_02_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_01_05

theorem row_05_02_01_06 : b4RowContribution (![5, 7, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 8, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 8 + 14 = 34
    decide
  have hzsq : (∑ i, (((![5, 7, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 334 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 8^2 + 14^2 = 334
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_01_06

theorem weighted_05_02_01_06 : b4RawGapContribution ![5, 2, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 1, 6] = b4GapPatternWeight 2 1 6 * 0 :=
      b4GapContribution_from_row 5 2 1 6 0 row_05_02_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_01_06

theorem row_05_02_01_07 : b4RowContribution (![5, 7, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 8, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 8 + 15 = 35
    decide
  have hzsq : (∑ i, (((![5, 7, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 363 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 8^2 + 15^2 = 363
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_01_07

theorem weighted_05_02_01_07 : b4RawGapContribution ![5, 2, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 1, 7] = b4GapPatternWeight 2 1 7 * 0 :=
      b4GapContribution_from_row 5 2 1 7 0 row_05_02_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_01_07

theorem row_05_02_01_08 : b4RowContribution (![5, 7, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 8, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 8 + 16 = 36
    decide
  have hzsq : (∑ i, (((![5, 7, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 394 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 8^2 + 16^2 = 394
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_01_08

theorem weighted_05_02_01_08 : b4RawGapContribution ![5, 2, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 1, 8] = b4GapPatternWeight 2 1 8 * 0 :=
      b4GapContribution_from_row 5 2 1 8 0 row_05_02_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_01_08

theorem row_05_02_01_09 : b4RowContribution (![5, 7, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 7, 8, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 7 + 8 + 17 = 37
    decide
  have hzsq : (∑ i, (((![5, 7, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 427 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 7^2 + 8^2 + 17^2 = 427
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_02_01_09

theorem weighted_05_02_01_09 : b4RawGapContribution ![5, 2, 1, 9] = 0 := by
  calc
    b4RawGapContribution ![5, 2, 1, 9] = b4GapPatternWeight 2 1 9 * 0 :=
      b4GapContribution_from_row 5 2 1 9 0 row_05_02_01_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_02_01_09

def dvalues_05_02_01 : Fin 10 → ℕ := ![0, 0, 0, 0, 480, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_02_01

theorem dblock_05_02_01 : b4GapPatternDBlock 5 2 1 = 480 := by
  calc
    b4GapPatternDBlock 5 2 1 = ∑ d : Fin 10, dvalues_05_02_01 d := by
      apply b4GapDBlock_of_rows 5 2 1 dvalues_05_02_01
      intro d
      fin_cases d
      · exact weighted_05_02_01_00
      · exact weighted_05_02_01_01
      · exact weighted_05_02_01_02
      · exact weighted_05_02_01_03
      · exact weighted_05_02_01_04
      · exact weighted_05_02_01_05
      · exact weighted_05_02_01_06
      · exact weighted_05_02_01_07
      · exact weighted_05_02_01_08
      · exact weighted_05_02_01_09
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_02_01

end Paper7MomentGapNumeric
