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

def layers_02_06_02_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 24, 26, 27, 26, 24, 21, 18, 15, 12, 9, 6], ![1, 4, 10, 19, 31, 46, 64, 85, 109, 135, 162, 187, 208, 223, 232, 235, 232, 223, 208]]
#print axioms Paper7MomentGapNumeric.layers_02_06_02_00

theorem cells_02_06_02_00 : QTableValid (![2, 8, 10, 10] : Fin 4 → ℕ) layers_02_06_02_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_06_02_00

theorem valid_02_06_02_00 :
    SparseRowValid (![2, 8, 10, 10] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_02_06_02_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 8, 10, 10] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 2 + 8 + 10 + 10 = 30
      decide
    have hzsq : (∑ i, (((![2, 8, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 268 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 8^2 + 10^2 + 10^2 = 268
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_06_02_00
#print axioms Paper7MomentGapNumeric.valid_02_06_02_00

def qvalues_02_06_02_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 85, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_06_02_00

theorem row_02_06_02_00 : b4RowContribution (![2, 8, 10, 10] : Fin 4 → ℕ) = 85 := by
  calc
    b4RowContribution (![2, 8, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_02_06_02_00) :=
      sparseRow_sound (![2, 8, 10, 10] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_02_06_02_00) valid_02_06_02_00
    _ = 85 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_06_02_00 Q := by
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
        _ = 85 := by decide
#print axioms Paper7MomentGapNumeric.row_02_06_02_00

theorem weighted_02_06_02_00 : b4RawGapContribution ![2, 6, 2, 0] = 1020 := by
  calc
    b4RawGapContribution ![2, 6, 2, 0] = b4GapPatternWeight 6 2 0 * 85 :=
      b4GapContribution_from_row 2 6 2 0 85 row_02_06_02_00
    _ = 1020 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_02_00

theorem row_02_06_02_01 : b4RowContribution (![2, 8, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 10, 11] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 10 + 11 = 31
    decide
  have hzsq : (∑ i, (((![2, 8, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 289 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 10^2 + 11^2 = 289
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_02_01

theorem weighted_02_06_02_01 : b4RawGapContribution ![2, 6, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 2, 1] = b4GapPatternWeight 6 2 1 * 0 :=
      b4GapContribution_from_row 2 6 2 1 0 row_02_06_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_02_01

theorem row_02_06_02_02 : b4RowContribution (![2, 8, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 10, 12] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 10 + 12 = 32
    decide
  have hzsq : (∑ i, (((![2, 8, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 312 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 10^2 + 12^2 = 312
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_02_02

theorem weighted_02_06_02_02 : b4RawGapContribution ![2, 6, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 2, 2] = b4GapPatternWeight 6 2 2 * 0 :=
      b4GapContribution_from_row 2 6 2 2 0 row_02_06_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_02_02

theorem row_02_06_02_03 : b4RowContribution (![2, 8, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 10, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 10 + 13 = 33
    decide
  have hzsq : (∑ i, (((![2, 8, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 337 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 10^2 + 13^2 = 337
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_02_03

theorem weighted_02_06_02_03 : b4RawGapContribution ![2, 6, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 2, 3] = b4GapPatternWeight 6 2 3 * 0 :=
      b4GapContribution_from_row 2 6 2 3 0 row_02_06_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_02_03

theorem row_02_06_02_04 : b4RowContribution (![2, 8, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 10, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 10 + 14 = 34
    decide
  have hzsq : (∑ i, (((![2, 8, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 364 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 10^2 + 14^2 = 364
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_02_04

theorem weighted_02_06_02_04 : b4RawGapContribution ![2, 6, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 2, 4] = b4GapPatternWeight 6 2 4 * 0 :=
      b4GapContribution_from_row 2 6 2 4 0 row_02_06_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_02_04

theorem row_02_06_02_05 : b4RowContribution (![2, 8, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 10, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 10 + 15 = 35
    decide
  have hzsq : (∑ i, (((![2, 8, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 393 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 10^2 + 15^2 = 393
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_02_05

theorem weighted_02_06_02_05 : b4RawGapContribution ![2, 6, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 2, 5] = b4GapPatternWeight 6 2 5 * 0 :=
      b4GapContribution_from_row 2 6 2 5 0 row_02_06_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_02_05

theorem row_02_06_02_06 : b4RowContribution (![2, 8, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 10, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 10 + 16 = 36
    decide
  have hzsq : (∑ i, (((![2, 8, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 424 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 10^2 + 16^2 = 424
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_02_06

theorem weighted_02_06_02_06 : b4RawGapContribution ![2, 6, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 2, 6] = b4GapPatternWeight 6 2 6 * 0 :=
      b4GapContribution_from_row 2 6 2 6 0 row_02_06_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_02_06

theorem row_02_06_02_07 : b4RowContribution (![2, 8, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 8, 10, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 8 + 10 + 17 = 37
    decide
  have hzsq : (∑ i, (((![2, 8, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 457 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 8^2 + 10^2 + 17^2 = 457
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_06_02_07

theorem weighted_02_06_02_07 : b4RawGapContribution ![2, 6, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 6, 2, 7] = b4GapPatternWeight 6 2 7 * 0 :=
      b4GapContribution_from_row 2 6 2 7 0 row_02_06_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_06_02_07

def dvalues_02_06_02 : Fin 8 → ℕ := ![1020, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_06_02

theorem dblock_02_06_02 : b4GapPatternDBlock 2 6 2 = 1020 := by
  calc
    b4GapPatternDBlock 2 6 2 = ∑ d : Fin 8, dvalues_02_06_02 d := by
      apply b4GapDBlock_of_rows 2 6 2 dvalues_02_06_02
      intro d
      fin_cases d
      · exact weighted_02_06_02_00
      · exact weighted_02_06_02_01
      · exact weighted_02_06_02_02
      · exact weighted_02_06_02_03
      · exact weighted_02_06_02_04
      · exact weighted_02_06_02_05
      · exact weighted_02_06_02_06
      · exact weighted_02_06_02_07
    _ = 1020 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_06_02

end Paper7MomentGapNumeric
