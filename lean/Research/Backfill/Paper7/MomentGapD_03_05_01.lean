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

def layers_03_05_01_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 4, 4, 4, 4, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 14, 18, 22, 26, 30, 33, 34, 33, 30, 26, 22, 18, 14, 10, 6], ![1, 4, 10, 20, 34, 52, 74, 100, 130, 163, 196, 226, 250, 266, 274, 274, 266, 250, 226]]
#print axioms Paper7MomentGapNumeric.layers_03_05_01_00

theorem cells_03_05_01_00 : QTableValid (![3, 8, 9, 9] : Fin 4 → ℕ) layers_03_05_01_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_05_01_00

theorem valid_03_05_01_00 :
    SparseRowValid (![3, 8, 9, 9] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_03_05_01_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 8, 9, 9] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 3 + 8 + 9 + 9 = 29
      decide
    have hzsq : (∑ i, (((![3, 8, 9, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 235 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 8^2 + 9^2 + 9^2 = 235
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_05_01_00
#print axioms Paper7MomentGapNumeric.valid_03_05_01_00

def qvalues_03_05_01_00 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_05_01_00

theorem row_03_05_01_00 : b4RowContribution (![3, 8, 9, 9] : Fin 4 → ℕ) = 4 := by
  calc
    b4RowContribution (![3, 8, 9, 9] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_03_05_01_00) :=
      sparseRow_sound (![3, 8, 9, 9] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_03_05_01_00) valid_03_05_01_00
    _ = 4 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_05_01_00 Q := by
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
#print axioms Paper7MomentGapNumeric.row_03_05_01_00

theorem weighted_03_05_01_00 : b4RawGapContribution ![3, 5, 1, 0] = 48 := by
  calc
    b4RawGapContribution ![3, 5, 1, 0] = b4GapPatternWeight 5 1 0 * 4 :=
      b4GapContribution_from_row 3 5 1 0 4 row_03_05_01_00
    _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_01_00

theorem row_03_05_01_01 : b4RowContribution (![3, 8, 9, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 9, 10] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 9 + 10 = 30
    decide
  have hzsq : (∑ i, (((![3, 8, 9, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 254 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 9^2 + 10^2 = 254
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_01_01

theorem weighted_03_05_01_01 : b4RawGapContribution ![3, 5, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 1, 1] = b4GapPatternWeight 5 1 1 * 0 :=
      b4GapContribution_from_row 3 5 1 1 0 row_03_05_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_01_01

theorem row_03_05_01_02 : b4RowContribution (![3, 8, 9, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 9, 11] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 9 + 11 = 31
    decide
  have hzsq : (∑ i, (((![3, 8, 9, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 275 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 9^2 + 11^2 = 275
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_01_02

theorem weighted_03_05_01_02 : b4RawGapContribution ![3, 5, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 1, 2] = b4GapPatternWeight 5 1 2 * 0 :=
      b4GapContribution_from_row 3 5 1 2 0 row_03_05_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_01_02

theorem row_03_05_01_03 : b4RowContribution (![3, 8, 9, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 9, 12] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 9 + 12 = 32
    decide
  have hzsq : (∑ i, (((![3, 8, 9, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 298 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 9^2 + 12^2 = 298
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_01_03

theorem weighted_03_05_01_03 : b4RawGapContribution ![3, 5, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 1, 3] = b4GapPatternWeight 5 1 3 * 0 :=
      b4GapContribution_from_row 3 5 1 3 0 row_03_05_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_01_03

theorem row_03_05_01_04 : b4RowContribution (![3, 8, 9, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 9, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 9 + 13 = 33
    decide
  have hzsq : (∑ i, (((![3, 8, 9, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 323 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 9^2 + 13^2 = 323
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_01_04

theorem weighted_03_05_01_04 : b4RawGapContribution ![3, 5, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 1, 4] = b4GapPatternWeight 5 1 4 * 0 :=
      b4GapContribution_from_row 3 5 1 4 0 row_03_05_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_01_04

theorem row_03_05_01_05 : b4RowContribution (![3, 8, 9, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 9, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 9 + 14 = 34
    decide
  have hzsq : (∑ i, (((![3, 8, 9, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 350 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 9^2 + 14^2 = 350
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_01_05

theorem weighted_03_05_01_05 : b4RawGapContribution ![3, 5, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 1, 5] = b4GapPatternWeight 5 1 5 * 0 :=
      b4GapContribution_from_row 3 5 1 5 0 row_03_05_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_01_05

theorem row_03_05_01_06 : b4RowContribution (![3, 8, 9, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 9, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 9 + 15 = 35
    decide
  have hzsq : (∑ i, (((![3, 8, 9, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 379 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 9^2 + 15^2 = 379
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_01_06

theorem weighted_03_05_01_06 : b4RawGapContribution ![3, 5, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 1, 6] = b4GapPatternWeight 5 1 6 * 0 :=
      b4GapContribution_from_row 3 5 1 6 0 row_03_05_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_01_06

theorem row_03_05_01_07 : b4RowContribution (![3, 8, 9, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 9, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 9 + 16 = 36
    decide
  have hzsq : (∑ i, (((![3, 8, 9, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 410 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 9^2 + 16^2 = 410
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_01_07

theorem weighted_03_05_01_07 : b4RawGapContribution ![3, 5, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 1, 7] = b4GapPatternWeight 5 1 7 * 0 :=
      b4GapContribution_from_row 3 5 1 7 0 row_03_05_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_01_07

theorem row_03_05_01_08 : b4RowContribution (![3, 8, 9, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 8, 9, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 8 + 9 + 17 = 37
    decide
  have hzsq : (∑ i, (((![3, 8, 9, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 443 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 8^2 + 9^2 + 17^2 = 443
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_05_01_08

theorem weighted_03_05_01_08 : b4RawGapContribution ![3, 5, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 5, 1, 8] = b4GapPatternWeight 5 1 8 * 0 :=
      b4GapContribution_from_row 3 5 1 8 0 row_03_05_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_05_01_08

def dvalues_03_05_01 : Fin 9 → ℕ := ![48, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_05_01

theorem dblock_03_05_01 : b4GapPatternDBlock 3 5 1 = 48 := by
  calc
    b4GapPatternDBlock 3 5 1 = ∑ d : Fin 9, dvalues_03_05_01 d := by
      apply b4GapDBlock_of_rows 3 5 1 dvalues_03_05_01
      intro d
      fin_cases d
      · exact weighted_03_05_01_00
      · exact weighted_03_05_01_01
      · exact weighted_03_05_01_02
      · exact weighted_03_05_01_03
      · exact weighted_03_05_01_04
      · exact weighted_03_05_01_05
      · exact weighted_03_05_01_06
      · exact weighted_03_05_01_07
      · exact weighted_03_05_01_08
    _ = 48 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_05_01

end Paper7MomentGapNumeric
