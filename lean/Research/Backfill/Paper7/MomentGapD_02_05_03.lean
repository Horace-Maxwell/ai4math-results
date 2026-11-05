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

theorem row_02_05_03_00 : b4RowContribution (![2, 7, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 10, 10] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 10 + 10 = 29
    decide
  have hzsq : (∑ i, (((![2, 7, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 253 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 10^2 + 10^2 = 253
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_03_00

theorem weighted_02_05_03_00 : b4RawGapContribution ![2, 5, 3, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 3, 0] = b4GapPatternWeight 5 3 0 * 0 :=
      b4GapContribution_from_row 2 5 3 0 0 row_02_05_03_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_03_00

def layers_02_05_03_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 21, 23, 24, 24, 23, 21, 18, 15, 12, 9, 6, 3], ![1, 4, 10, 19, 31, 46, 64, 85, 108, 132, 156, 179, 199, 214, 223, 226, 223, 214, 199]]
#print axioms Paper7MomentGapNumeric.layers_02_05_03_01

theorem cells_02_05_03_01 : QTableValid (![2, 7, 10, 11] : Fin 4 → ℕ) layers_02_05_03_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_05_03_01

theorem valid_02_05_03_01 :
    SparseRowValid (![2, 7, 10, 11] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_05_03_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 7, 10, 11] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 2 + 7 + 10 + 11 = 30
      decide
    have hzsq : (∑ i, (((![2, 7, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 274 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 7^2 + 10^2 + 11^2 = 274
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_05_03_01
#print axioms Paper7MomentGapNumeric.valid_02_05_03_01

def qvalues_02_05_03_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_05_03_01

theorem row_02_05_03_01 : b4RowContribution (![2, 7, 10, 11] : Fin 4 → ℕ) = 31 := by
  calc
    b4RowContribution (![2, 7, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_02_05_03_01) :=
      sparseRow_sound (![2, 7, 10, 11] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_02_05_03_01) valid_02_05_03_01
    _ = 31 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_05_03_01 Q := by
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
        _ = 31 := by decide
#print axioms Paper7MomentGapNumeric.row_02_05_03_01

theorem weighted_02_05_03_01 : b4RawGapContribution ![2, 5, 3, 1] = 744 := by
  calc
    b4RawGapContribution ![2, 5, 3, 1] = b4GapPatternWeight 5 3 1 * 31 :=
      b4GapContribution_from_row 2 5 3 1 31 row_02_05_03_01
    _ = 744 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_03_01

theorem row_02_05_03_02 : b4RowContribution (![2, 7, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 10, 12] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 10 + 12 = 31
    decide
  have hzsq : (∑ i, (((![2, 7, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 297 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 10^2 + 12^2 = 297
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_03_02

theorem weighted_02_05_03_02 : b4RawGapContribution ![2, 5, 3, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 3, 2] = b4GapPatternWeight 5 3 2 * 0 :=
      b4GapContribution_from_row 2 5 3 2 0 row_02_05_03_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_03_02

theorem row_02_05_03_03 : b4RowContribution (![2, 7, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 10, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 10 + 13 = 32
    decide
  have hzsq : (∑ i, (((![2, 7, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 322 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 10^2 + 13^2 = 322
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_03_03

theorem weighted_02_05_03_03 : b4RawGapContribution ![2, 5, 3, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 3, 3] = b4GapPatternWeight 5 3 3 * 0 :=
      b4GapContribution_from_row 2 5 3 3 0 row_02_05_03_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_03_03

theorem row_02_05_03_04 : b4RowContribution (![2, 7, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 10, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 10 + 14 = 33
    decide
  have hzsq : (∑ i, (((![2, 7, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 349 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 10^2 + 14^2 = 349
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_03_04

theorem weighted_02_05_03_04 : b4RawGapContribution ![2, 5, 3, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 3, 4] = b4GapPatternWeight 5 3 4 * 0 :=
      b4GapContribution_from_row 2 5 3 4 0 row_02_05_03_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_03_04

theorem row_02_05_03_05 : b4RowContribution (![2, 7, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 10, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 10 + 15 = 34
    decide
  have hzsq : (∑ i, (((![2, 7, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 378 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 10^2 + 15^2 = 378
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_03_05

theorem weighted_02_05_03_05 : b4RawGapContribution ![2, 5, 3, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 3, 5] = b4GapPatternWeight 5 3 5 * 0 :=
      b4GapContribution_from_row 2 5 3 5 0 row_02_05_03_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_03_05

theorem row_02_05_03_06 : b4RowContribution (![2, 7, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 10, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 10 + 16 = 35
    decide
  have hzsq : (∑ i, (((![2, 7, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 409 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 10^2 + 16^2 = 409
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_03_06

theorem weighted_02_05_03_06 : b4RawGapContribution ![2, 5, 3, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 3, 6] = b4GapPatternWeight 5 3 6 * 0 :=
      b4GapContribution_from_row 2 5 3 6 0 row_02_05_03_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_03_06

theorem row_02_05_03_07 : b4RowContribution (![2, 7, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 10, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 10 + 17 = 36
    decide
  have hzsq : (∑ i, (((![2, 7, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 442 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 10^2 + 17^2 = 442
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_03_07

theorem weighted_02_05_03_07 : b4RawGapContribution ![2, 5, 3, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 3, 7] = b4GapPatternWeight 5 3 7 * 0 :=
      b4GapContribution_from_row 2 5 3 7 0 row_02_05_03_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_03_07

theorem row_02_05_03_08 : b4RowContribution (![2, 7, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 7, 10, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 7 + 10 + 18 = 37
    decide
  have hzsq : (∑ i, (((![2, 7, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 477 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 7^2 + 10^2 + 18^2 = 477
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_05_03_08

theorem weighted_02_05_03_08 : b4RawGapContribution ![2, 5, 3, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 5, 3, 8] = b4GapPatternWeight 5 3 8 * 0 :=
      b4GapContribution_from_row 2 5 3 8 0 row_02_05_03_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_05_03_08

def dvalues_02_05_03 : Fin 9 → ℕ := ![0, 744, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_05_03

theorem dblock_02_05_03 : b4GapPatternDBlock 2 5 3 = 744 := by
  calc
    b4GapPatternDBlock 2 5 3 = ∑ d : Fin 9, dvalues_02_05_03 d := by
      apply b4GapDBlock_of_rows 2 5 3 dvalues_02_05_03
      intro d
      fin_cases d
      · exact weighted_02_05_03_00
      · exact weighted_02_05_03_01
      · exact weighted_02_05_03_02
      · exact weighted_02_05_03_03
      · exact weighted_02_05_03_04
      · exact weighted_02_05_03_05
      · exact weighted_02_05_03_06
      · exact weighted_02_05_03_07
      · exact weighted_02_05_03_08
    _ = 744 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_05_03

end Paper7MomentGapNumeric
