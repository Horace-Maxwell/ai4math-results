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

def layers_04_00_07_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 19, 22, 24, 25, 25, 25, 25, 24, 22, 19, 15, 10, 6, 3], ![1, 4, 10, 20, 35, 54, 76, 100, 125, 150, 175, 200, 223, 242, 255, 260, 255, 242, 223]]
#print axioms Paper7MomentGapNumeric.layers_04_00_07_00

theorem cells_04_00_07_00 : QTableValid (![4, 4, 11, 11] : Fin 4 → ℕ) layers_04_00_07_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_00_07_00

theorem valid_04_00_07_00 :
    SparseRowValid (![4, 4, 11, 11] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_04_00_07_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 4, 11, 11] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 4 + 4 + 11 + 11 = 30
      decide
    have hzsq : (∑ i, (((![4, 4, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 274 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 4^2 + 11^2 + 11^2 = 274
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_00_07_00
#print axioms Paper7MomentGapNumeric.valid_04_00_07_00

def qvalues_04_00_07_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_00_07_00

theorem row_04_00_07_00 : b4RowContribution (![4, 4, 11, 11] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![4, 4, 11, 11] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_04_00_07_00) :=
      sparseRow_sound (![4, 4, 11, 11] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_04_00_07_00) valid_04_00_07_00
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_00_07_00 Q := by
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
#print axioms Paper7MomentGapNumeric.row_04_00_07_00

theorem weighted_04_00_07_00 : b4RawGapContribution ![4, 0, 7, 0] = 210 := by
  calc
    b4RawGapContribution ![4, 0, 7, 0] = b4GapPatternWeight 0 7 0 * 35 :=
      b4GapContribution_from_row 4 0 7 0 35 row_04_00_07_00
    _ = 210 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_07_00

theorem row_04_00_07_01 : b4RowContribution (![4, 4, 11, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 11, 12] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 11 + 12 = 31
    decide
  have hzsq : (∑ i, (((![4, 4, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 297 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 11^2 + 12^2 = 297
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_07_01

theorem weighted_04_00_07_01 : b4RawGapContribution ![4, 0, 7, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 7, 1] = b4GapPatternWeight 0 7 1 * 0 :=
      b4GapContribution_from_row 4 0 7 1 0 row_04_00_07_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_07_01

theorem row_04_00_07_02 : b4RowContribution (![4, 4, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 11, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 11 + 13 = 32
    decide
  have hzsq : (∑ i, (((![4, 4, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 322 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 11^2 + 13^2 = 322
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_07_02

theorem weighted_04_00_07_02 : b4RawGapContribution ![4, 0, 7, 2] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 7, 2] = b4GapPatternWeight 0 7 2 * 0 :=
      b4GapContribution_from_row 4 0 7 2 0 row_04_00_07_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_07_02

theorem row_04_00_07_03 : b4RowContribution (![4, 4, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 11, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 11 + 14 = 33
    decide
  have hzsq : (∑ i, (((![4, 4, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 349 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 11^2 + 14^2 = 349
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_07_03

theorem weighted_04_00_07_03 : b4RawGapContribution ![4, 0, 7, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 7, 3] = b4GapPatternWeight 0 7 3 * 0 :=
      b4GapContribution_from_row 4 0 7 3 0 row_04_00_07_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_07_03

theorem row_04_00_07_04 : b4RowContribution (![4, 4, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 11, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 11 + 15 = 34
    decide
  have hzsq : (∑ i, (((![4, 4, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 378 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 11^2 + 15^2 = 378
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_07_04

theorem weighted_04_00_07_04 : b4RawGapContribution ![4, 0, 7, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 7, 4] = b4GapPatternWeight 0 7 4 * 0 :=
      b4GapContribution_from_row 4 0 7 4 0 row_04_00_07_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_07_04

theorem row_04_00_07_05 : b4RowContribution (![4, 4, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 11, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 11 + 16 = 35
    decide
  have hzsq : (∑ i, (((![4, 4, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 409 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 11^2 + 16^2 = 409
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_07_05

theorem weighted_04_00_07_05 : b4RawGapContribution ![4, 0, 7, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 7, 5] = b4GapPatternWeight 0 7 5 * 0 :=
      b4GapContribution_from_row 4 0 7 5 0 row_04_00_07_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_07_05

theorem row_04_00_07_06 : b4RowContribution (![4, 4, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 11, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 11 + 17 = 36
    decide
  have hzsq : (∑ i, (((![4, 4, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 442 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 11^2 + 17^2 = 442
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_07_06

theorem weighted_04_00_07_06 : b4RawGapContribution ![4, 0, 7, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 7, 6] = b4GapPatternWeight 0 7 6 * 0 :=
      b4GapContribution_from_row 4 0 7 6 0 row_04_00_07_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_07_06

theorem row_04_00_07_07 : b4RowContribution (![4, 4, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 11, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 11 + 18 = 37
    decide
  have hzsq : (∑ i, (((![4, 4, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 477 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 11^2 + 18^2 = 477
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_07_07

theorem weighted_04_00_07_07 : b4RawGapContribution ![4, 0, 7, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 7, 7] = b4GapPatternWeight 0 7 7 * 0 :=
      b4GapContribution_from_row 4 0 7 7 0 row_04_00_07_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_07_07

def dvalues_04_00_07 : Fin 8 → ℕ := ![210, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_00_07

theorem dblock_04_00_07 : b4GapPatternDBlock 4 0 7 = 210 := by
  calc
    b4GapPatternDBlock 4 0 7 = ∑ d : Fin 8, dvalues_04_00_07 d := by
      apply b4GapDBlock_of_rows 4 0 7 dvalues_04_00_07
      intro d
      fin_cases d
      · exact weighted_04_00_07_00
      · exact weighted_04_00_07_01
      · exact weighted_04_00_07_02
      · exact weighted_04_00_07_03
      · exact weighted_04_00_07_04
      · exact weighted_04_00_07_05
      · exact weighted_04_00_07_06
      · exact weighted_04_00_07_07
    _ = 210 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_00_07

end Paper7MomentGapNumeric
