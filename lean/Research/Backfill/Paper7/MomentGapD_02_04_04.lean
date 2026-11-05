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

theorem row_02_04_04_00 : b4RowContribution (![2, 6, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 10, 10] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 10 + 10 = 28
    decide
  have hzsq : (∑ i, (((![2, 6, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 240 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 10^2 + 10^2 = 240
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_04_00

theorem weighted_02_04_04_00 : b4RawGapContribution ![2, 4, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 4, 0] = b4GapPatternWeight 4 4 0 * 0 :=
      b4GapContribution_from_row 2 4 4 0 0 row_02_04_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_04_00

theorem row_02_04_04_01 : b4RowContribution (![2, 6, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 10, 11] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 10 + 11 = 29
    decide
  have hzsq : (∑ i, (((![2, 6, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 261 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 10^2 + 11^2 = 261
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_04_01

theorem weighted_02_04_04_01 : b4RawGapContribution ![2, 4, 4, 1] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 4, 1] = b4GapPatternWeight 4 4 1 * 0 :=
      b4GapContribution_from_row 2 4 4 1 0 row_02_04_04_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_04_01

def layers_02_04_04_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 3, 3, 3, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 9, 12, 15, 18, 20, 21, 21, 21, 20, 18, 15, 12, 9, 6, 3, 1], ![1, 4, 10, 19, 31, 46, 64, 84, 105, 126, 147, 167, 185, 199, 208, 211, 208, 199, 185]]
#print axioms Paper7MomentGapNumeric.layers_02_04_04_02

theorem cells_02_04_04_02 : QTableValid (![2, 6, 10, 12] : Fin 4 → ℕ) layers_02_04_04_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_04_04_02

theorem valid_02_04_04_02 :
    SparseRowValid (![2, 6, 10, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_02_04_04_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 6, 10, 12] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 2 + 6 + 10 + 12 = 30
      decide
    have hzsq : (∑ i, (((![2, 6, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 284 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 6^2 + 10^2 + 12^2 = 284
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_04_04_02
#print axioms Paper7MomentGapNumeric.valid_02_04_04_02

def qvalues_02_04_04_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_04_04_02

theorem row_02_04_04_02 : b4RowContribution (![2, 6, 10, 12] : Fin 4 → ℕ) = 46 := by
  calc
    b4RowContribution (![2, 6, 10, 12] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_02_04_04_02) :=
      sparseRow_sound (![2, 6, 10, 12] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_02_04_04_02) valid_02_04_04_02
    _ = 46 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_04_04_02 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 46 := by decide
#print axioms Paper7MomentGapNumeric.row_02_04_04_02

theorem weighted_02_04_04_02 : b4RawGapContribution ![2, 4, 4, 2] = 1104 := by
  calc
    b4RawGapContribution ![2, 4, 4, 2] = b4GapPatternWeight 4 4 2 * 46 :=
      b4GapContribution_from_row 2 4 4 2 46 row_02_04_04_02
    _ = 1104 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_04_02

theorem row_02_04_04_03 : b4RowContribution (![2, 6, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 10, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 10 + 13 = 31
    decide
  have hzsq : (∑ i, (((![2, 6, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 309 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 10^2 + 13^2 = 309
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_04_03

theorem weighted_02_04_04_03 : b4RawGapContribution ![2, 4, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 4, 3] = b4GapPatternWeight 4 4 3 * 0 :=
      b4GapContribution_from_row 2 4 4 3 0 row_02_04_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_04_03

theorem row_02_04_04_04 : b4RowContribution (![2, 6, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 10, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 10 + 14 = 32
    decide
  have hzsq : (∑ i, (((![2, 6, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 336 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 10^2 + 14^2 = 336
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_04_04

theorem weighted_02_04_04_04 : b4RawGapContribution ![2, 4, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 4, 4] = b4GapPatternWeight 4 4 4 * 0 :=
      b4GapContribution_from_row 2 4 4 4 0 row_02_04_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_04_04

theorem row_02_04_04_05 : b4RowContribution (![2, 6, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 10, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 10 + 15 = 33
    decide
  have hzsq : (∑ i, (((![2, 6, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 365 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 10^2 + 15^2 = 365
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_04_05

theorem weighted_02_04_04_05 : b4RawGapContribution ![2, 4, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 4, 5] = b4GapPatternWeight 4 4 5 * 0 :=
      b4GapContribution_from_row 2 4 4 5 0 row_02_04_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_04_05

theorem row_02_04_04_06 : b4RowContribution (![2, 6, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 10, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 10 + 16 = 34
    decide
  have hzsq : (∑ i, (((![2, 6, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 396 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 10^2 + 16^2 = 396
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_04_06

theorem weighted_02_04_04_06 : b4RawGapContribution ![2, 4, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 4, 6] = b4GapPatternWeight 4 4 6 * 0 :=
      b4GapContribution_from_row 2 4 4 6 0 row_02_04_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_04_06

theorem row_02_04_04_07 : b4RowContribution (![2, 6, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 10, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 10 + 17 = 35
    decide
  have hzsq : (∑ i, (((![2, 6, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 429 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 10^2 + 17^2 = 429
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_04_07

theorem weighted_02_04_04_07 : b4RawGapContribution ![2, 4, 4, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 4, 7] = b4GapPatternWeight 4 4 7 * 0 :=
      b4GapContribution_from_row 2 4 4 7 0 row_02_04_04_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_04_07

theorem row_02_04_04_08 : b4RowContribution (![2, 6, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 10, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 10 + 18 = 36
    decide
  have hzsq : (∑ i, (((![2, 6, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 464 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 10^2 + 18^2 = 464
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_04_08

theorem weighted_02_04_04_08 : b4RawGapContribution ![2, 4, 4, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 4, 8] = b4GapPatternWeight 4 4 8 * 0 :=
      b4GapContribution_from_row 2 4 4 8 0 row_02_04_04_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_04_08

theorem row_02_04_04_09 : b4RowContribution (![2, 6, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 6, 10, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 6 + 10 + 19 = 37
    decide
  have hzsq : (∑ i, (((![2, 6, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 501 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 6^2 + 10^2 + 19^2 = 501
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_04_04_09

theorem weighted_02_04_04_09 : b4RawGapContribution ![2, 4, 4, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 4, 4, 9] = b4GapPatternWeight 4 4 9 * 0 :=
      b4GapContribution_from_row 2 4 4 9 0 row_02_04_04_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_04_04_09

def dvalues_02_04_04 : Fin 10 → ℕ := ![0, 0, 1104, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_04_04

theorem dblock_02_04_04 : b4GapPatternDBlock 2 4 4 = 1104 := by
  calc
    b4GapPatternDBlock 2 4 4 = ∑ d : Fin 10, dvalues_02_04_04 d := by
      apply b4GapDBlock_of_rows 2 4 4 dvalues_02_04_04
      intro d
      fin_cases d
      · exact weighted_02_04_04_00
      · exact weighted_02_04_04_01
      · exact weighted_02_04_04_02
      · exact weighted_02_04_04_03
      · exact weighted_02_04_04_04
      · exact weighted_02_04_04_05
      · exact weighted_02_04_04_06
      · exact weighted_02_04_04_07
      · exact weighted_02_04_04_08
      · exact weighted_02_04_04_09
    _ = 1104 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_04_04

end Paper7MomentGapNumeric
