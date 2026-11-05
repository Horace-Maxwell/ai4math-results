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

def layers_00_05_05_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 6, 6, 6, 6, 5, 4, 3, 2, 1, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 27, 33, 39, 45, 51, 55, 57, 57, 55, 51, 45, 39, 33]]
#print axioms Paper7MomentGapNumeric.layers_00_05_05_00

theorem cells_00_05_05_00 : QTableValid (![0, 5, 10, 10] : Fin 4 → ℕ) layers_00_05_05_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_05_05_00

theorem valid_00_05_05_00 :
    SparseRowValid (![0, 5, 10, 10] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_00_05_05_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 5, 10, 10] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 5 + 10 + 10 = 25
      decide
    have hzsq : (∑ i, (((![0, 5, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 225 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 5^2 + 10^2 + 10^2 = 225
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_05_05_00
#print axioms Paper7MomentGapNumeric.valid_00_05_05_00

def qvalues_00_05_05_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 57, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_05_05_00

theorem row_00_05_05_00 : b4RowContribution (![0, 5, 10, 10] : Fin 4 → ℕ) = 84 := by
  calc
    b4RowContribution (![0, 5, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({6, 12} : Finset (Fin 19)) (fun _ => layers_00_05_05_00) :=
      sparseRow_sound (![0, 5, 10, 10] : Fin 4 → ℕ) ({6, 12} : Finset (Fin 19)) (fun _ => layers_00_05_05_00) valid_00_05_05_00
    _ = 84 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_05_05_00 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 84 := by decide
#print axioms Paper7MomentGapNumeric.row_00_05_05_00

theorem weighted_00_05_05_00 : b4RawGapContribution ![0, 5, 5, 0] = 1008 := by
  calc
    b4RawGapContribution ![0, 5, 5, 0] = b4GapPatternWeight 5 5 0 * 84 :=
      b4GapContribution_from_row 0 5 5 0 84 row_00_05_05_00
    _ = 1008 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_05_00

theorem row_00_05_05_01 : b4RowContribution (![0, 5, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 10, 11] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 10 + 11 = 26
    decide
  have hzsq : (∑ i, (((![0, 5, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 246 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 10^2 + 11^2 = 246
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_05_01

theorem weighted_00_05_05_01 : b4RawGapContribution ![0, 5, 5, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 5, 1] = b4GapPatternWeight 5 5 1 * 0 :=
      b4GapContribution_from_row 0 5 5 1 0 row_00_05_05_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_05_01

theorem row_00_05_05_02 : b4RowContribution (![0, 5, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 10, 12] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 10 + 12 = 27
    decide
  have hzsq : (∑ i, (((![0, 5, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 269 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 10^2 + 12^2 = 269
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_05_02

theorem weighted_00_05_05_02 : b4RawGapContribution ![0, 5, 5, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 5, 2] = b4GapPatternWeight 5 5 2 * 0 :=
      b4GapContribution_from_row 0 5 5 2 0 row_00_05_05_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_05_02

theorem row_00_05_05_03 : b4RowContribution (![0, 5, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 10, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 10 + 13 = 28
    decide
  have hzsq : (∑ i, (((![0, 5, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 294 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 10^2 + 13^2 = 294
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_05_03

theorem weighted_00_05_05_03 : b4RawGapContribution ![0, 5, 5, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 5, 3] = b4GapPatternWeight 5 5 3 * 0 :=
      b4GapContribution_from_row 0 5 5 3 0 row_00_05_05_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_05_03

theorem row_00_05_05_04 : b4RowContribution (![0, 5, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 10, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 10 + 14 = 29
    decide
  have hzsq : (∑ i, (((![0, 5, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 321 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 10^2 + 14^2 = 321
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_05_04

theorem weighted_00_05_05_04 : b4RawGapContribution ![0, 5, 5, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 5, 4] = b4GapPatternWeight 5 5 4 * 0 :=
      b4GapContribution_from_row 0 5 5 4 0 row_00_05_05_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_05_04

theorem row_00_05_05_05 : b4RowContribution (![0, 5, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 10, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 10 + 15 = 30
    decide
  have hzsq : (∑ i, (((![0, 5, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 350 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 10^2 + 15^2 = 350
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_05_05

theorem weighted_00_05_05_05 : b4RawGapContribution ![0, 5, 5, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 5, 5] = b4GapPatternWeight 5 5 5 * 0 :=
      b4GapContribution_from_row 0 5 5 5 0 row_00_05_05_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_05_05

theorem row_00_05_05_06 : b4RowContribution (![0, 5, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 10, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 10 + 16 = 31
    decide
  have hzsq : (∑ i, (((![0, 5, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 381 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 10^2 + 16^2 = 381
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_05_06

theorem weighted_00_05_05_06 : b4RawGapContribution ![0, 5, 5, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 5, 6] = b4GapPatternWeight 5 5 6 * 0 :=
      b4GapContribution_from_row 0 5 5 6 0 row_00_05_05_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_05_06

theorem row_00_05_05_07 : b4RowContribution (![0, 5, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 10, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 10 + 17 = 32
    decide
  have hzsq : (∑ i, (((![0, 5, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 414 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 10^2 + 17^2 = 414
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_05_07

theorem weighted_00_05_05_07 : b4RawGapContribution ![0, 5, 5, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 5, 7] = b4GapPatternWeight 5 5 7 * 0 :=
      b4GapContribution_from_row 0 5 5 7 0 row_00_05_05_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_05_07

theorem row_00_05_05_08 : b4RowContribution (![0, 5, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 10, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 10 + 18 = 33
    decide
  have hzsq : (∑ i, (((![0, 5, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 449 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 10^2 + 18^2 = 449
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_05_08

theorem weighted_00_05_05_08 : b4RawGapContribution ![0, 5, 5, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 5, 8] = b4GapPatternWeight 5 5 8 * 0 :=
      b4GapContribution_from_row 0 5 5 8 0 row_00_05_05_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_05_08

theorem row_00_05_05_09 : b4RowContribution (![0, 5, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 10, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 10 + 19 = 34
    decide
  have hzsq : (∑ i, (((![0, 5, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 486 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 10^2 + 19^2 = 486
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_05_09

theorem weighted_00_05_05_09 : b4RawGapContribution ![0, 5, 5, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 5, 9] = b4GapPatternWeight 5 5 9 * 0 :=
      b4GapContribution_from_row 0 5 5 9 0 row_00_05_05_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_05_09

theorem row_00_05_05_10 : b4RowContribution (![0, 5, 10, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 10, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 10 + 20 = 35
    decide
  have hzsq : (∑ i, (((![0, 5, 10, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 525 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 10^2 + 20^2 = 525
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_05_10

theorem weighted_00_05_05_10 : b4RawGapContribution ![0, 5, 5, 10] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 5, 10] = b4GapPatternWeight 5 5 10 * 0 :=
      b4GapContribution_from_row 0 5 5 10 0 row_00_05_05_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_05_10

theorem row_00_05_05_11 : b4RowContribution (![0, 5, 10, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 10, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 10 + 21 = 36
    decide
  have hzsq : (∑ i, (((![0, 5, 10, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 566 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 10^2 + 21^2 = 566
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_05_11

theorem weighted_00_05_05_11 : b4RawGapContribution ![0, 5, 5, 11] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 5, 11] = b4GapPatternWeight 5 5 11 * 0 :=
      b4GapContribution_from_row 0 5 5 11 0 row_00_05_05_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_05_11

theorem row_00_05_05_12 : b4RowContribution (![0, 5, 10, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 5, 10, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 5 + 10 + 22 = 37
    decide
  have hzsq : (∑ i, (((![0, 5, 10, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 609 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 5^2 + 10^2 + 22^2 = 609
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_05_05_12

theorem weighted_00_05_05_12 : b4RawGapContribution ![0, 5, 5, 12] = 0 := by
  calc
    b4RawGapContribution ![0, 5, 5, 12] = b4GapPatternWeight 5 5 12 * 0 :=
      b4GapContribution_from_row 0 5 5 12 0 row_00_05_05_12
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_05_05_12

def dvalues_00_05_05 : Fin 13 → ℕ := ![1008, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_05_05

theorem dblock_00_05_05 : b4GapPatternDBlock 0 5 5 = 1008 := by
  calc
    b4GapPatternDBlock 0 5 5 = ∑ d : Fin 13, dvalues_00_05_05 d := by
      apply b4GapDBlock_of_rows 0 5 5 dvalues_00_05_05
      intro d
      fin_cases d
      · exact weighted_00_05_05_00
      · exact weighted_00_05_05_01
      · exact weighted_00_05_05_02
      · exact weighted_00_05_05_03
      · exact weighted_00_05_05_04
      · exact weighted_00_05_05_05
      · exact weighted_00_05_05_06
      · exact weighted_00_05_05_07
      · exact weighted_00_05_05_08
      · exact weighted_00_05_05_09
      · exact weighted_00_05_05_10
      · exact weighted_00_05_05_11
      · exact weighted_00_05_05_12
    _ = 1008 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_05_05

end Paper7MomentGapNumeric
