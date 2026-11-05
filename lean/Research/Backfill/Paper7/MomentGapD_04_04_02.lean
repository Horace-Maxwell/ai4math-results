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

def layers_04_04_02_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 20, 25, 30, 35, 39, 42, 43, 42, 39, 35, 30, 25, 20, 15], ![1, 4, 10, 20, 35, 55, 80, 110, 145, 184, 226, 268, 307, 340, 365, 380, 385, 380, 365]]
#print axioms Paper7MomentGapNumeric.layers_04_04_02_00

theorem cells_04_04_02_00 : QTableValid (![4, 8, 10, 10] : Fin 4 → ℕ) layers_04_04_02_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_04_02_00

theorem valid_04_04_02_00 :
    SparseRowValid (![4, 8, 10, 10] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_04_04_02_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 8, 10, 10] : Fin 4 → ℕ) i) = 32 := by
      rw [Fin.sum_univ_four]
      change 4 + 8 + 10 + 10 = 32
      decide
    have hzsq : (∑ i, (((![4, 8, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 280 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 8^2 + 10^2 + 10^2 = 280
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_04_02_00
#print axioms Paper7MomentGapNumeric.valid_04_04_02_00

def qvalues_04_04_02_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_04_02_00

theorem row_04_04_02_00 : b4RowContribution (![4, 8, 10, 10] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![4, 8, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_04_04_02_00) :=
      sparseRow_sound (![4, 8, 10, 10] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_04_04_02_00) valid_04_04_02_00
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_04_02_00 Q := by
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
#print axioms Paper7MomentGapNumeric.row_04_04_02_00

theorem weighted_04_04_02_00 : b4RawGapContribution ![4, 4, 2, 0] = 420 := by
  calc
    b4RawGapContribution ![4, 4, 2, 0] = b4GapPatternWeight 4 2 0 * 35 :=
      b4GapContribution_from_row 4 4 2 0 35 row_04_04_02_00
    _ = 420 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_02_00

theorem row_04_04_02_01 : b4RowContribution (![4, 8, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 10, 11] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 10 + 11 = 33
    decide
  have hzsq : (∑ i, (((![4, 8, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 301 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 10^2 + 11^2 = 301
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_02_01

theorem weighted_04_04_02_01 : b4RawGapContribution ![4, 4, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 2, 1] = b4GapPatternWeight 4 2 1 * 0 :=
      b4GapContribution_from_row 4 4 2 1 0 row_04_04_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_02_01

theorem row_04_04_02_02 : b4RowContribution (![4, 8, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 10, 12] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 10 + 12 = 34
    decide
  have hzsq : (∑ i, (((![4, 8, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 324 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 10^2 + 12^2 = 324
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_02_02

theorem weighted_04_04_02_02 : b4RawGapContribution ![4, 4, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 2, 2] = b4GapPatternWeight 4 2 2 * 0 :=
      b4GapContribution_from_row 4 4 2 2 0 row_04_04_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_02_02

theorem row_04_04_02_03 : b4RowContribution (![4, 8, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 10, 13] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 10 + 13 = 35
    decide
  have hzsq : (∑ i, (((![4, 8, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 349 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 10^2 + 13^2 = 349
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_02_03

theorem weighted_04_04_02_03 : b4RawGapContribution ![4, 4, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 2, 3] = b4GapPatternWeight 4 2 3 * 0 :=
      b4GapContribution_from_row 4 4 2 3 0 row_04_04_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_02_03

theorem row_04_04_02_04 : b4RowContribution (![4, 8, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 10, 14] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 10 + 14 = 36
    decide
  have hzsq : (∑ i, (((![4, 8, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 376 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 10^2 + 14^2 = 376
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_02_04

theorem weighted_04_04_02_04 : b4RawGapContribution ![4, 4, 2, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 2, 4] = b4GapPatternWeight 4 2 4 * 0 :=
      b4GapContribution_from_row 4 4 2 4 0 row_04_04_02_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_02_04

theorem row_04_04_02_05 : b4RowContribution (![4, 8, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 8, 10, 15] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 8 + 10 + 15 = 37
    decide
  have hzsq : (∑ i, (((![4, 8, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 405 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 8^2 + 10^2 + 15^2 = 405
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_04_02_05

theorem weighted_04_04_02_05 : b4RawGapContribution ![4, 4, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 4, 2, 5] = b4GapPatternWeight 4 2 5 * 0 :=
      b4GapContribution_from_row 4 4 2 5 0 row_04_04_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_04_02_05

def dvalues_04_04_02 : Fin 6 → ℕ := ![420, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_04_02

theorem dblock_04_04_02 : b4GapPatternDBlock 4 4 2 = 420 := by
  calc
    b4GapPatternDBlock 4 4 2 = ∑ d : Fin 6, dvalues_04_04_02 d := by
      apply b4GapDBlock_of_rows 4 4 2 dvalues_04_04_02
      intro d
      fin_cases d
      · exact weighted_04_04_02_00
      · exact weighted_04_04_02_01
      · exact weighted_04_04_02_02
      · exact weighted_04_04_02_03
      · exact weighted_04_04_02_04
      · exact weighted_04_04_02_05
    _ = 420 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_04_02

end Paper7MomentGapNumeric
