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

theorem row_06_02_01_00 : b4RowContribution (![6, 8, 9, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 8, 9, 9] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 6 + 8 + 9 + 9 = 32
    decide
  have hzsq : (∑ i, (((![6, 8, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 262 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 8^2 + 9^2 + 9^2 = 262
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_02_01_00

theorem weighted_06_02_01_00 : b4RawGapContribution ![6, 2, 1, 0] = 0 := by
  calc
    b4RawGapContribution ![6, 2, 1, 0] = b4GapPatternWeight 2 1 0 * 0 :=
      b4GapContribution_from_row 6 2 1 0 0 row_06_02_01_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_02_01_00

def layers_06_02_01_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 35, 42, 48, 52, 54, 54, 52, 48, 42, 35, 28, 21], ![1, 4, 10, 20, 35, 56, 84, 119, 161, 209, 261, 314, 365, 411, 449, 476, 490, 490, 476]]
#print axioms Paper7MomentGapNumeric.layers_06_02_01_01

theorem cells_06_02_01_01 : QTableValid (![6, 8, 9, 10] : Fin 4 → ℕ) layers_06_02_01_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_06_02_01_01

theorem valid_06_02_01_01 :
    SparseRowValid (![6, 8, 9, 10] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_06_02_01_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![6, 8, 9, 10] : Fin 4 → ℕ) i) = 33 := by
      rw [Fin.sum_univ_four]
      change 6 + 8 + 9 + 10 = 33
      decide
    have hzsq : (∑ i, (((![6, 8, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 281 := by
      rw [Fin.sum_univ_four]
      change (6 : ℤ)^2 + 8^2 + 9^2 + 10^2 = 281
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_06_02_01_01
#print axioms Paper7MomentGapNumeric.valid_06_02_01_01

def qvalues_06_02_01_01 : Fin 19 → ℕ := ![0, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_06_02_01_01

theorem row_06_02_01_01 : b4RowContribution (![6, 8, 9, 10] : Fin 4 → ℕ) = 10 := by
  calc
    b4RowContribution (![6, 8, 9, 10] : Fin 4 → ℕ) =
        sparseRowValue ({2} : Finset (Fin 19)) (fun _ => layers_06_02_01_01) :=
      sparseRow_sound (![6, 8, 9, 10] : Fin 4 → ℕ) ({2} : Finset (Fin 19)) (fun _ => layers_06_02_01_01) valid_06_02_01_01
    _ = 10 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_06_02_01_01 Q := by
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
#print axioms Paper7MomentGapNumeric.row_06_02_01_01

theorem weighted_06_02_01_01 : b4RawGapContribution ![6, 2, 1, 1] = 240 := by
  calc
    b4RawGapContribution ![6, 2, 1, 1] = b4GapPatternWeight 2 1 1 * 10 :=
      b4GapContribution_from_row 6 2 1 1 10 row_06_02_01_01
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_02_01_01

theorem row_06_02_01_02 : b4RowContribution (![6, 8, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 8, 9, 11] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 6 + 8 + 9 + 11 = 34
    decide
  have hzsq : (∑ i, (((![6, 8, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 302 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 8^2 + 9^2 + 11^2 = 302
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_02_01_02

theorem weighted_06_02_01_02 : b4RawGapContribution ![6, 2, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![6, 2, 1, 2] = b4GapPatternWeight 2 1 2 * 0 :=
      b4GapContribution_from_row 6 2 1 2 0 row_06_02_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_02_01_02

theorem row_06_02_01_03 : b4RowContribution (![6, 8, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 8, 9, 12] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 6 + 8 + 9 + 12 = 35
    decide
  have hzsq : (∑ i, (((![6, 8, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 8^2 + 9^2 + 12^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_02_01_03

theorem weighted_06_02_01_03 : b4RawGapContribution ![6, 2, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![6, 2, 1, 3] = b4GapPatternWeight 2 1 3 * 0 :=
      b4GapContribution_from_row 6 2 1 3 0 row_06_02_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_02_01_03

theorem row_06_02_01_04 : b4RowContribution (![6, 8, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 8, 9, 13] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 6 + 8 + 9 + 13 = 36
    decide
  have hzsq : (∑ i, (((![6, 8, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 350 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 8^2 + 9^2 + 13^2 = 350
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_02_01_04

theorem weighted_06_02_01_04 : b4RawGapContribution ![6, 2, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![6, 2, 1, 4] = b4GapPatternWeight 2 1 4 * 0 :=
      b4GapContribution_from_row 6 2 1 4 0 row_06_02_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_02_01_04

theorem row_06_02_01_05 : b4RowContribution (![6, 8, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 8, 9, 14] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 6 + 8 + 9 + 14 = 37
    decide
  have hzsq : (∑ i, (((![6, 8, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 377 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 8^2 + 9^2 + 14^2 = 377
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_02_01_05

theorem weighted_06_02_01_05 : b4RawGapContribution ![6, 2, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![6, 2, 1, 5] = b4GapPatternWeight 2 1 5 * 0 :=
      b4GapContribution_from_row 6 2 1 5 0 row_06_02_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_02_01_05

def dvalues_06_02_01 : Fin 6 → ℕ := ![0, 240, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_06_02_01

theorem dblock_06_02_01 : b4GapPatternDBlock 6 2 1 = 240 := by
  calc
    b4GapPatternDBlock 6 2 1 = ∑ d : Fin 6, dvalues_06_02_01 d := by
      apply b4GapDBlock_of_rows 6 2 1 dvalues_06_02_01
      intro d
      fin_cases d
      · exact weighted_06_02_01_00
      · exact weighted_06_02_01_01
      · exact weighted_06_02_01_02
      · exact weighted_06_02_01_03
      · exact weighted_06_02_01_04
      · exact weighted_06_02_01_05
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.dblock_06_02_01

end Paper7MomentGapNumeric
