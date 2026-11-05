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

theorem row_00_08_02_00 : b4RowContribution (![0, 8, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 10, 10] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 10 + 10 = 28
    decide
  have hzsq : (∑ i, (((![0, 8, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 264 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 10^2 + 10^2 = 264
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_02_00

theorem weighted_00_08_02_00 : b4RawGapContribution ![0, 8, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 2, 0] = b4GapPatternWeight 8 2 0 * 0 :=
      b4GapContribution_from_row 0 8 2 0 0 row_00_08_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_02_00

def layers_00_08_02_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 9, 9, 8, 7, 6, 5, 4, 3, 2, 1], ![1, 3, 6, 10, 15, 21, 28, 36, 45, 54, 63, 71, 77, 81, 83, 83, 81, 77, 71]]
#print axioms Paper7MomentGapNumeric.layers_00_08_02_01

theorem cells_00_08_02_01 : QTableValid (![0, 8, 10, 11] : Fin 4 → ℕ) layers_00_08_02_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_08_02_01

theorem valid_00_08_02_01 :
    SparseRowValid (![0, 8, 10, 11] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_00_08_02_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 8, 10, 11] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 0 + 8 + 10 + 11 = 29
      decide
    have hzsq : (∑ i, (((![0, 8, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 285 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 8^2 + 10^2 + 11^2 = 285
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_08_02_01
#print axioms Paper7MomentGapNumeric.valid_00_08_02_01

def qvalues_00_08_02_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_08_02_01

theorem row_00_08_02_01 : b4RowContribution (![0, 8, 10, 11] : Fin 4 → ℕ) = 28 := by
  calc
    b4RowContribution (![0, 8, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({6} : Finset (Fin 19)) (fun _ => layers_00_08_02_01) :=
      sparseRow_sound (![0, 8, 10, 11] : Fin 4 → ℕ) ({6} : Finset (Fin 19)) (fun _ => layers_00_08_02_01) valid_00_08_02_01
    _ = 28 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_08_02_01 Q := by
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
        _ = 28 := by decide
#print axioms Paper7MomentGapNumeric.row_00_08_02_01

theorem weighted_00_08_02_01 : b4RawGapContribution ![0, 8, 2, 1] = 672 := by
  calc
    b4RawGapContribution ![0, 8, 2, 1] = b4GapPatternWeight 8 2 1 * 28 :=
      b4GapContribution_from_row 0 8 2 1 28 row_00_08_02_01
    _ = 672 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_02_01

theorem row_00_08_02_02 : b4RowContribution (![0, 8, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 10, 12] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 10 + 12 = 30
    decide
  have hzsq : (∑ i, (((![0, 8, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 308 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 10^2 + 12^2 = 308
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_02_02

theorem weighted_00_08_02_02 : b4RawGapContribution ![0, 8, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 2, 2] = b4GapPatternWeight 8 2 2 * 0 :=
      b4GapContribution_from_row 0 8 2 2 0 row_00_08_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_02_02

theorem row_00_08_02_03 : b4RowContribution (![0, 8, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 10, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 10 + 13 = 31
    decide
  have hzsq : (∑ i, (((![0, 8, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 333 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 10^2 + 13^2 = 333
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_02_03

theorem weighted_00_08_02_03 : b4RawGapContribution ![0, 8, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 2, 3] = b4GapPatternWeight 8 2 3 * 0 :=
      b4GapContribution_from_row 0 8 2 3 0 row_00_08_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_02_03

theorem row_00_08_02_04 : b4RowContribution (![0, 8, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 10, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 10 + 14 = 32
    decide
  have hzsq : (∑ i, (((![0, 8, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 360 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 10^2 + 14^2 = 360
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_02_04

theorem weighted_00_08_02_04 : b4RawGapContribution ![0, 8, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 2, 4] = b4GapPatternWeight 8 2 4 * 0 :=
      b4GapContribution_from_row 0 8 2 4 0 row_00_08_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_02_04

theorem row_00_08_02_05 : b4RowContribution (![0, 8, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 10, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 10 + 15 = 33
    decide
  have hzsq : (∑ i, (((![0, 8, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 389 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 10^2 + 15^2 = 389
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_02_05

theorem weighted_00_08_02_05 : b4RawGapContribution ![0, 8, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 2, 5] = b4GapPatternWeight 8 2 5 * 0 :=
      b4GapContribution_from_row 0 8 2 5 0 row_00_08_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_02_05

theorem row_00_08_02_06 : b4RowContribution (![0, 8, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 10, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 10 + 16 = 34
    decide
  have hzsq : (∑ i, (((![0, 8, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 420 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 10^2 + 16^2 = 420
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_02_06

theorem weighted_00_08_02_06 : b4RawGapContribution ![0, 8, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 2, 6] = b4GapPatternWeight 8 2 6 * 0 :=
      b4GapContribution_from_row 0 8 2 6 0 row_00_08_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_02_06

theorem row_00_08_02_07 : b4RowContribution (![0, 8, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 10, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 10 + 17 = 35
    decide
  have hzsq : (∑ i, (((![0, 8, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 453 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 10^2 + 17^2 = 453
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_02_07

theorem weighted_00_08_02_07 : b4RawGapContribution ![0, 8, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 2, 7] = b4GapPatternWeight 8 2 7 * 0 :=
      b4GapContribution_from_row 0 8 2 7 0 row_00_08_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_02_07

theorem row_00_08_02_08 : b4RowContribution (![0, 8, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 10, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 10 + 18 = 36
    decide
  have hzsq : (∑ i, (((![0, 8, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 488 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 10^2 + 18^2 = 488
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_02_08

theorem weighted_00_08_02_08 : b4RawGapContribution ![0, 8, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 2, 8] = b4GapPatternWeight 8 2 8 * 0 :=
      b4GapContribution_from_row 0 8 2 8 0 row_00_08_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_02_08

theorem row_00_08_02_09 : b4RowContribution (![0, 8, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 8, 10, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 8 + 10 + 19 = 37
    decide
  have hzsq : (∑ i, (((![0, 8, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 525 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 8^2 + 10^2 + 19^2 = 525
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_08_02_09

theorem weighted_00_08_02_09 : b4RawGapContribution ![0, 8, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![0, 8, 2, 9] = b4GapPatternWeight 8 2 9 * 0 :=
      b4GapContribution_from_row 0 8 2 9 0 row_00_08_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_08_02_09

def dvalues_00_08_02 : Fin 10 → ℕ := ![0, 672, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_08_02

theorem dblock_00_08_02 : b4GapPatternDBlock 0 8 2 = 672 := by
  calc
    b4GapPatternDBlock 0 8 2 = ∑ d : Fin 10, dvalues_00_08_02 d := by
      apply b4GapDBlock_of_rows 0 8 2 dvalues_00_08_02
      intro d
      fin_cases d
      · exact weighted_00_08_02_00
      · exact weighted_00_08_02_01
      · exact weighted_00_08_02_02
      · exact weighted_00_08_02_03
      · exact weighted_00_08_02_04
      · exact weighted_00_08_02_05
      · exact weighted_00_08_02_06
      · exact weighted_00_08_02_07
      · exact weighted_00_08_02_08
      · exact weighted_00_08_02_09
    _ = 672 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_08_02

end Paper7MomentGapNumeric
