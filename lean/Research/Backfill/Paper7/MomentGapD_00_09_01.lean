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

def layers_00_09_01_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 9, 8, 7, 6, 5, 4, 3, 2], ![1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 65, 73, 79, 83, 85, 85, 83, 79, 73]]
#print axioms Paper7MomentGapNumeric.layers_00_09_01_00

theorem cells_00_09_01_00 : QTableValid (![0, 9, 10, 10] : Fin 4 → ℕ) layers_00_09_01_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_00_09_01_00

theorem valid_00_09_01_00 :
    SparseRowValid (![0, 9, 10, 10] : Fin 4 → ℕ) ({2, 8} : Finset (Fin 19)) (fun _ => layers_00_09_01_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 9, 10, 10] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 0 + 9 + 10 + 10 = 29
      decide
    have hzsq : (∑ i, (((![0, 9, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 281 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 9^2 + 10^2 + 10^2 = 281
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_00_09_01_00
#print axioms Paper7MomentGapNumeric.valid_00_09_01_00

def qvalues_00_09_01_00 : Fin 19 → ℕ := ![0, 0, 6, 0, 0, 0, 0, 0, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_00_09_01_00

theorem row_00_09_01_00 : b4RowContribution (![0, 9, 10, 10] : Fin 4 → ℕ) = 51 := by
  calc
    b4RowContribution (![0, 9, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({2, 8} : Finset (Fin 19)) (fun _ => layers_00_09_01_00) :=
      sparseRow_sound (![0, 9, 10, 10] : Fin 4 → ℕ) ({2, 8} : Finset (Fin 19)) (fun _ => layers_00_09_01_00) valid_00_09_01_00
    _ = 51 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_00_09_01_00 Q := by
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
        _ = 51 := by decide
#print axioms Paper7MomentGapNumeric.row_00_09_01_00

theorem weighted_00_09_01_00 : b4RawGapContribution ![0, 9, 1, 0] = 612 := by
  calc
    b4RawGapContribution ![0, 9, 1, 0] = b4GapPatternWeight 9 1 0 * 51 :=
      b4GapContribution_from_row 0 9 1 0 51 row_00_09_01_00
    _ = 612 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_01_00

theorem row_00_09_01_01 : b4RowContribution (![0, 9, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 10, 11] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 10 + 11 = 30
    decide
  have hzsq : (∑ i, (((![0, 9, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 302 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 10^2 + 11^2 = 302
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_01_01

theorem weighted_00_09_01_01 : b4RawGapContribution ![0, 9, 1, 1] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 1, 1] = b4GapPatternWeight 9 1 1 * 0 :=
      b4GapContribution_from_row 0 9 1 1 0 row_00_09_01_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_01_01

theorem row_00_09_01_02 : b4RowContribution (![0, 9, 10, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 10, 12] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 10 + 12 = 31
    decide
  have hzsq : (∑ i, (((![0, 9, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 10^2 + 12^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_01_02

theorem weighted_00_09_01_02 : b4RawGapContribution ![0, 9, 1, 2] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 1, 2] = b4GapPatternWeight 9 1 2 * 0 :=
      b4GapContribution_from_row 0 9 1 2 0 row_00_09_01_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_01_02

theorem row_00_09_01_03 : b4RowContribution (![0, 9, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 10, 13] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 10 + 13 = 32
    decide
  have hzsq : (∑ i, (((![0, 9, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 350 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 10^2 + 13^2 = 350
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_01_03

theorem weighted_00_09_01_03 : b4RawGapContribution ![0, 9, 1, 3] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 1, 3] = b4GapPatternWeight 9 1 3 * 0 :=
      b4GapContribution_from_row 0 9 1 3 0 row_00_09_01_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_01_03

theorem row_00_09_01_04 : b4RowContribution (![0, 9, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 10, 14] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 10 + 14 = 33
    decide
  have hzsq : (∑ i, (((![0, 9, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 377 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 10^2 + 14^2 = 377
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_01_04

theorem weighted_00_09_01_04 : b4RawGapContribution ![0, 9, 1, 4] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 1, 4] = b4GapPatternWeight 9 1 4 * 0 :=
      b4GapContribution_from_row 0 9 1 4 0 row_00_09_01_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_01_04

theorem row_00_09_01_05 : b4RowContribution (![0, 9, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 10, 15] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 10 + 15 = 34
    decide
  have hzsq : (∑ i, (((![0, 9, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 406 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 10^2 + 15^2 = 406
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_01_05

theorem weighted_00_09_01_05 : b4RawGapContribution ![0, 9, 1, 5] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 1, 5] = b4GapPatternWeight 9 1 5 * 0 :=
      b4GapContribution_from_row 0 9 1 5 0 row_00_09_01_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_01_05

theorem row_00_09_01_06 : b4RowContribution (![0, 9, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 10, 16] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 10 + 16 = 35
    decide
  have hzsq : (∑ i, (((![0, 9, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 437 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 10^2 + 16^2 = 437
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_01_06

theorem weighted_00_09_01_06 : b4RawGapContribution ![0, 9, 1, 6] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 1, 6] = b4GapPatternWeight 9 1 6 * 0 :=
      b4GapContribution_from_row 0 9 1 6 0 row_00_09_01_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_01_06

theorem row_00_09_01_07 : b4RowContribution (![0, 9, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 10, 17] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 10 + 17 = 36
    decide
  have hzsq : (∑ i, (((![0, 9, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 470 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 10^2 + 17^2 = 470
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_01_07

theorem weighted_00_09_01_07 : b4RawGapContribution ![0, 9, 1, 7] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 1, 7] = b4GapPatternWeight 9 1 7 * 0 :=
      b4GapContribution_from_row 0 9 1 7 0 row_00_09_01_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_01_07

theorem row_00_09_01_08 : b4RowContribution (![0, 9, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 9, 10, 18] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 9 + 10 + 18 = 37
    decide
  have hzsq : (∑ i, (((![0, 9, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 505 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 9^2 + 10^2 + 18^2 = 505
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_00_09_01_08

theorem weighted_00_09_01_08 : b4RawGapContribution ![0, 9, 1, 8] = 0 := by
  calc
    b4RawGapContribution ![0, 9, 1, 8] = b4GapPatternWeight 9 1 8 * 0 :=
      b4GapContribution_from_row 0 9 1 8 0 row_00_09_01_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_00_09_01_08

def dvalues_00_09_01 : Fin 9 → ℕ := ![612, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_00_09_01

theorem dblock_00_09_01 : b4GapPatternDBlock 0 9 1 = 612 := by
  calc
    b4GapPatternDBlock 0 9 1 = ∑ d : Fin 9, dvalues_00_09_01 d := by
      apply b4GapDBlock_of_rows 0 9 1 dvalues_00_09_01
      intro d
      fin_cases d
      · exact weighted_00_09_01_00
      · exact weighted_00_09_01_01
      · exact weighted_00_09_01_02
      · exact weighted_00_09_01_03
      · exact weighted_00_09_01_04
      · exact weighted_00_09_01_05
      · exact weighted_00_09_01_06
      · exact weighted_00_09_01_07
      · exact weighted_00_09_01_08
    _ = 612 := by decide
#print axioms Paper7MomentGapNumeric.dblock_00_09_01

end Paper7MomentGapNumeric
