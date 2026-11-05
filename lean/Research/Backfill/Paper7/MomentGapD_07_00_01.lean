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

theorem row_07_00_01_00 : b4RowContribution (![7, 7, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 8, 8] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 8 + 8 = 30
    decide
  have hzsq : (∑ i, (((![7, 7, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 226 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 8^2 + 8^2 = 226
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_01_00

theorem weighted_07_00_01_00 : b4RawGapContribution ![7, 0, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 1, 0] = b4GapPatternWeight 0 1 0 * 0 :=
      b4GapContribution_from_row 7 0 1 0 0 row_07_00_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_01_00

theorem row_07_00_01_01 : b4RowContribution (![7, 7, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 8, 9] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 8 + 9 = 31
    decide
  have hzsq : (∑ i, (((![7, 7, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 243 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 8^2 + 9^2 = 243
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_01_01

theorem weighted_07_00_01_01 : b4RawGapContribution ![7, 0, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 1, 1] = b4GapPatternWeight 0 1 1 * 0 :=
      b4GapContribution_from_row 7 0 1 1 0 row_07_00_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_01_01

theorem row_07_00_01_02 : b4RowContribution (![7, 7, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 8, 10] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 8 + 10 = 32
    decide
  have hzsq : (∑ i, (((![7, 7, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 262 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 8^2 + 10^2 = 262
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_01_02

theorem weighted_07_00_01_02 : b4RawGapContribution ![7, 0, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 1, 2] = b4GapPatternWeight 0 1 2 * 0 :=
      b4GapContribution_from_row 7 0 1 2 0 row_07_00_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_01_02

def layers_07_00_01_03 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 36, 43, 48, 51, 52, 51, 48, 43, 36, 28, 21, 15], ![1, 4, 10, 20, 35, 56, 84, 120, 163, 211, 262, 314, 364, 409, 446, 472, 485, 485, 472]]
#print axioms Paper7MomentGapNumeric.layers_07_00_01_03

theorem cells_07_00_01_03 : QTableValid (![7, 7, 8, 11] : Fin 4 → ℕ) layers_07_00_01_03 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_07_00_01_03

theorem valid_07_00_01_03 :
    SparseRowValid (![7, 7, 8, 11] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_07_00_01_03) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![7, 7, 8, 11] : Fin 4 → ℕ) i) = 33 := by
      rw [Fin.sum_univ_four]
      change 7 + 7 + 8 + 11 = 33
      decide
    have hzsq : (∑ i, (((![7, 7, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 283 := by
      rw [Fin.sum_univ_four]
      change (7 : ℤ)^2 + 7^2 + 8^2 + 11^2 = 283
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_07_00_01_03
#print axioms Paper7MomentGapNumeric.valid_07_00_01_03

def qvalues_07_00_01_03 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_07_00_01_03

theorem row_07_00_01_03 : b4RowContribution (![7, 7, 8, 11] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![7, 7, 8, 11] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_07_00_01_03) :=
      sparseRow_sound (![7, 7, 8, 11] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_07_00_01_03) valid_07_00_01_03
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_07_00_01_03 Q := by
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
#print axioms Paper7MomentGapNumeric.row_07_00_01_03

theorem weighted_07_00_01_03 : b4RawGapContribution ![7, 0, 1, 3] = 48 := by
  calc
    b4RawGapContribution ![7, 0, 1, 3] = b4GapPatternWeight 0 1 3 * 4 :=
      b4GapContribution_from_row 7 0 1 3 4 row_07_00_01_03
    _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_01_03

theorem row_07_00_01_04 : b4RowContribution (![7, 7, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 8, 12] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 8 + 12 = 34
    decide
  have hzsq : (∑ i, (((![7, 7, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 306 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 8^2 + 12^2 = 306
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_01_04

theorem weighted_07_00_01_04 : b4RawGapContribution ![7, 0, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 1, 4] = b4GapPatternWeight 0 1 4 * 0 :=
      b4GapContribution_from_row 7 0 1 4 0 row_07_00_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_01_04

theorem row_07_00_01_05 : b4RowContribution (![7, 7, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 8, 13] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 8 + 13 = 35
    decide
  have hzsq : (∑ i, (((![7, 7, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 331 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 8^2 + 13^2 = 331
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_01_05

theorem weighted_07_00_01_05 : b4RawGapContribution ![7, 0, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 1, 5] = b4GapPatternWeight 0 1 5 * 0 :=
      b4GapContribution_from_row 7 0 1 5 0 row_07_00_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_01_05

theorem row_07_00_01_06 : b4RowContribution (![7, 7, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 8, 14] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 8 + 14 = 36
    decide
  have hzsq : (∑ i, (((![7, 7, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 358 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 8^2 + 14^2 = 358
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_01_06

theorem weighted_07_00_01_06 : b4RawGapContribution ![7, 0, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 1, 6] = b4GapPatternWeight 0 1 6 * 0 :=
      b4GapContribution_from_row 7 0 1 6 0 row_07_00_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_01_06

theorem row_07_00_01_07 : b4RowContribution (![7, 7, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 7, 8, 15] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 7 + 7 + 8 + 15 = 37
    decide
  have hzsq : (∑ i, (((![7, 7, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 387 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 7^2 + 8^2 + 15^2 = 387
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_00_01_07

theorem weighted_07_00_01_07 : b4RawGapContribution ![7, 0, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![7, 0, 1, 7] = b4GapPatternWeight 0 1 7 * 0 :=
      b4GapContribution_from_row 7 0 1 7 0 row_07_00_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_00_01_07

def dvalues_07_00_01 : Fin 8 → ℕ := ![0, 0, 0, 48, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_07_00_01

theorem dblock_07_00_01 : b4GapPatternDBlock 7 0 1 = 48 := by
  calc
    b4GapPatternDBlock 7 0 1 = ∑ d : Fin 8, dvalues_07_00_01 d := by
      apply b4GapDBlock_of_rows 7 0 1 dvalues_07_00_01
      intro d
      fin_cases d
      · exact weighted_07_00_01_00
      · exact weighted_07_00_01_01
      · exact weighted_07_00_01_02
      · exact weighted_07_00_01_03
      · exact weighted_07_00_01_04
      · exact weighted_07_00_01_05
      · exact weighted_07_00_01_06
      · exact weighted_07_00_01_07
    _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.dblock_07_00_01

end Paper7MomentGapNumeric
