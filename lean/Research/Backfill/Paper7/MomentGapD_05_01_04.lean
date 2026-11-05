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

theorem row_05_01_04_00 : b4RowContribution (![5, 6, 10, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 10, 10] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 10 + 10 = 31
    decide
  have hzsq : (∑ i, (((![5, 6, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 261 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 10^2 + 10^2 = 261
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_04_00

theorem weighted_05_01_04_00 : b4RawGapContribution ![5, 1, 4, 0] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 4, 0] = b4GapPatternWeight 1 4 0 * 0 :=
      b4GapContribution_from_row 5 1 4 0 0 row_05_01_04_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_04_00

def layers_05_01_04_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 27, 32, 36, 39, 41, 41, 39, 36, 32, 27, 21, 15, 10], ![1, 4, 10, 20, 35, 56, 83, 115, 151, 190, 231, 272, 310, 343, 369, 386, 392, 386, 369]]
#print axioms Paper7MomentGapNumeric.layers_05_01_04_01

theorem cells_05_01_04_01 : QTableValid (![5, 6, 10, 11] : Fin 4 → ℕ) layers_05_01_04_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_05_01_04_01

theorem valid_05_01_04_01 :
    SparseRowValid (![5, 6, 10, 11] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_05_01_04_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![5, 6, 10, 11] : Fin 4 → ℕ) i) = 32 := by
      rw [Fin.sum_univ_four]
      change 5 + 6 + 10 + 11 = 32
      decide
    have hzsq : (∑ i, (((![5, 6, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 282 := by
      rw [Fin.sum_univ_four]
      change (5 : ℤ)^2 + 6^2 + 10^2 + 11^2 = 282
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_05_01_04_01
#print axioms Paper7MomentGapNumeric.valid_05_01_04_01

def qvalues_05_01_04_01 : Fin 19 → ℕ := ![0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_05_01_04_01

theorem row_05_01_04_01 : b4RowContribution (![5, 6, 10, 11] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![5, 6, 10, 11] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_05_01_04_01) :=
      sparseRow_sound (![5, 6, 10, 11] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_05_01_04_01) valid_05_01_04_01
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_05_01_04_01 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 20 := by decide
#print axioms Paper7MomentGapNumeric.row_05_01_04_01

theorem weighted_05_01_04_01 : b4RawGapContribution ![5, 1, 4, 1] = 480 := by
  calc
    b4RawGapContribution ![5, 1, 4, 1] = b4GapPatternWeight 1 4 1 * 20 :=
      b4GapContribution_from_row 5 1 4 1 20 row_05_01_04_01
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_04_01

theorem row_05_01_04_02 : b4RowContribution (![5, 6, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 10, 12] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 10 + 12 = 33
    decide
  have hzsq : (∑ i, (((![5, 6, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 305 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 10^2 + 12^2 = 305
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_04_02

theorem weighted_05_01_04_02 : b4RawGapContribution ![5, 1, 4, 2] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 4, 2] = b4GapPatternWeight 1 4 2 * 0 :=
      b4GapContribution_from_row 5 1 4 2 0 row_05_01_04_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_04_02

theorem row_05_01_04_03 : b4RowContribution (![5, 6, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 10, 13] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 10 + 13 = 34
    decide
  have hzsq : (∑ i, (((![5, 6, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 330 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 10^2 + 13^2 = 330
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_04_03

theorem weighted_05_01_04_03 : b4RawGapContribution ![5, 1, 4, 3] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 4, 3] = b4GapPatternWeight 1 4 3 * 0 :=
      b4GapContribution_from_row 5 1 4 3 0 row_05_01_04_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_04_03

theorem row_05_01_04_04 : b4RowContribution (![5, 6, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 10, 14] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 10 + 14 = 35
    decide
  have hzsq : (∑ i, (((![5, 6, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 357 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 10^2 + 14^2 = 357
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_04_04

theorem weighted_05_01_04_04 : b4RawGapContribution ![5, 1, 4, 4] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 4, 4] = b4GapPatternWeight 1 4 4 * 0 :=
      b4GapContribution_from_row 5 1 4 4 0 row_05_01_04_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_04_04

theorem row_05_01_04_05 : b4RowContribution (![5, 6, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 10, 15] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 10 + 15 = 36
    decide
  have hzsq : (∑ i, (((![5, 6, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 386 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 10^2 + 15^2 = 386
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_04_05

theorem weighted_05_01_04_05 : b4RawGapContribution ![5, 1, 4, 5] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 4, 5] = b4GapPatternWeight 1 4 5 * 0 :=
      b4GapContribution_from_row 5 1 4 5 0 row_05_01_04_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_04_05

theorem row_05_01_04_06 : b4RowContribution (![5, 6, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![5, 6, 10, 16] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 5 + 6 + 10 + 16 = 37
    decide
  have hzsq : (∑ i, (((![5, 6, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 417 := by
    rw [Fin.sum_univ_four]
    change (5 : ℤ)^2 + 6^2 + 10^2 + 16^2 = 417
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_05_01_04_06

theorem weighted_05_01_04_06 : b4RawGapContribution ![5, 1, 4, 6] = 0 := by
  calc
    b4RawGapContribution ![5, 1, 4, 6] = b4GapPatternWeight 1 4 6 * 0 :=
      b4GapContribution_from_row 5 1 4 6 0 row_05_01_04_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_05_01_04_06

def dvalues_05_01_04 : Fin 7 → ℕ := ![0, 480, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_05_01_04

theorem dblock_05_01_04 : b4GapPatternDBlock 5 1 4 = 480 := by
  calc
    b4GapPatternDBlock 5 1 4 = ∑ d : Fin 7, dvalues_05_01_04 d := by
      apply b4GapDBlock_of_rows 5 1 4 dvalues_05_01_04
      intro d
      fin_cases d
      · exact weighted_05_01_04_00
      · exact weighted_05_01_04_01
      · exact weighted_05_01_04_02
      · exact weighted_05_01_04_03
      · exact weighted_05_01_04_04
      · exact weighted_05_01_04_05
      · exact weighted_05_01_04_06
    _ = 480 := by decide
#print axioms Paper7MomentGapNumeric.dblock_05_01_04

end Paper7MomentGapNumeric
