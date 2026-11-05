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

def layers_01_00_11_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 1, 0, 0, 0, 0], ![1, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 50, 48, 44, 40, 36, 32]]
#print axioms Paper7MomentGapNumeric.layers_01_00_11_00

theorem cells_01_00_11_00 : QTableValid (![1, 1, 12, 12] : Fin 4 → ℕ) layers_01_00_11_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_00_11_00

theorem valid_01_00_11_00 :
    SparseRowValid (![1, 1, 12, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_01_00_11_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 1, 12, 12] : Fin 4 → ℕ) i) = 26 := by
      rw [Fin.sum_univ_four]
      change 1 + 1 + 12 + 12 = 26
      decide
    have hzsq : (∑ i, (((![1, 1, 12, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 290 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 1^2 + 12^2 + 12^2 = 290
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_00_11_00
#print axioms Paper7MomentGapNumeric.valid_01_00_11_00

def qvalues_01_00_11_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_00_11_00

theorem row_01_00_11_00 : b4RowContribution (![1, 1, 12, 12] : Fin 4 → ℕ) = 32 := by
  calc
    b4RowContribution (![1, 1, 12, 12] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_01_00_11_00) :=
      sparseRow_sound (![1, 1, 12, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_01_00_11_00) valid_01_00_11_00
    _ = 32 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_00_11_00 Q := by
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
        _ = 32 := by decide
#print axioms Paper7MomentGapNumeric.row_01_00_11_00

theorem weighted_01_00_11_00 : b4RawGapContribution ![1, 0, 11, 0] = 192 := by
  calc
    b4RawGapContribution ![1, 0, 11, 0] = b4GapPatternWeight 0 11 0 * 32 :=
      b4GapContribution_from_row 1 0 11 0 32 row_01_00_11_00
    _ = 192 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_11_00

theorem row_01_00_11_01 : b4RowContribution (![1, 1, 12, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 12, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 12 + 13 = 27
    decide
  have hzsq : (∑ i, (((![1, 1, 12, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 315 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 12^2 + 13^2 = 315
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_11_01

theorem weighted_01_00_11_01 : b4RawGapContribution ![1, 0, 11, 1] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 11, 1] = b4GapPatternWeight 0 11 1 * 0 :=
      b4GapContribution_from_row 1 0 11 1 0 row_01_00_11_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_11_01

theorem row_01_00_11_02 : b4RowContribution (![1, 1, 12, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 12, 14] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 12 + 14 = 28
    decide
  have hzsq : (∑ i, (((![1, 1, 12, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 342 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 12^2 + 14^2 = 342
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_11_02

theorem weighted_01_00_11_02 : b4RawGapContribution ![1, 0, 11, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 11, 2] = b4GapPatternWeight 0 11 2 * 0 :=
      b4GapContribution_from_row 1 0 11 2 0 row_01_00_11_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_11_02

theorem row_01_00_11_03 : b4RowContribution (![1, 1, 12, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 12, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 12 + 15 = 29
    decide
  have hzsq : (∑ i, (((![1, 1, 12, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 371 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 12^2 + 15^2 = 371
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_11_03

theorem weighted_01_00_11_03 : b4RawGapContribution ![1, 0, 11, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 11, 3] = b4GapPatternWeight 0 11 3 * 0 :=
      b4GapContribution_from_row 1 0 11 3 0 row_01_00_11_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_11_03

theorem row_01_00_11_04 : b4RowContribution (![1, 1, 12, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 12, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 12 + 16 = 30
    decide
  have hzsq : (∑ i, (((![1, 1, 12, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 402 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 12^2 + 16^2 = 402
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_11_04

theorem weighted_01_00_11_04 : b4RawGapContribution ![1, 0, 11, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 11, 4] = b4GapPatternWeight 0 11 4 * 0 :=
      b4GapContribution_from_row 1 0 11 4 0 row_01_00_11_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_11_04

theorem row_01_00_11_05 : b4RowContribution (![1, 1, 12, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 12, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 12 + 17 = 31
    decide
  have hzsq : (∑ i, (((![1, 1, 12, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 435 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 12^2 + 17^2 = 435
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_11_05

theorem weighted_01_00_11_05 : b4RawGapContribution ![1, 0, 11, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 11, 5] = b4GapPatternWeight 0 11 5 * 0 :=
      b4GapContribution_from_row 1 0 11 5 0 row_01_00_11_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_11_05

theorem row_01_00_11_06 : b4RowContribution (![1, 1, 12, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 12, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 12 + 18 = 32
    decide
  have hzsq : (∑ i, (((![1, 1, 12, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 470 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 12^2 + 18^2 = 470
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_11_06

theorem weighted_01_00_11_06 : b4RawGapContribution ![1, 0, 11, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 11, 6] = b4GapPatternWeight 0 11 6 * 0 :=
      b4GapContribution_from_row 1 0 11 6 0 row_01_00_11_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_11_06

theorem row_01_00_11_07 : b4RowContribution (![1, 1, 12, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 12, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 12 + 19 = 33
    decide
  have hzsq : (∑ i, (((![1, 1, 12, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 507 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 12^2 + 19^2 = 507
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_11_07

theorem weighted_01_00_11_07 : b4RawGapContribution ![1, 0, 11, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 11, 7] = b4GapPatternWeight 0 11 7 * 0 :=
      b4GapContribution_from_row 1 0 11 7 0 row_01_00_11_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_11_07

theorem row_01_00_11_08 : b4RowContribution (![1, 1, 12, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 12, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 12 + 20 = 34
    decide
  have hzsq : (∑ i, (((![1, 1, 12, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 546 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 12^2 + 20^2 = 546
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_11_08

theorem weighted_01_00_11_08 : b4RawGapContribution ![1, 0, 11, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 11, 8] = b4GapPatternWeight 0 11 8 * 0 :=
      b4GapContribution_from_row 1 0 11 8 0 row_01_00_11_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_11_08

theorem row_01_00_11_09 : b4RowContribution (![1, 1, 12, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 12, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 12 + 21 = 35
    decide
  have hzsq : (∑ i, (((![1, 1, 12, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 587 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 12^2 + 21^2 = 587
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_11_09

theorem weighted_01_00_11_09 : b4RawGapContribution ![1, 0, 11, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 11, 9] = b4GapPatternWeight 0 11 9 * 0 :=
      b4GapContribution_from_row 1 0 11 9 0 row_01_00_11_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_11_09

theorem row_01_00_11_10 : b4RowContribution (![1, 1, 12, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 12, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 12 + 22 = 36
    decide
  have hzsq : (∑ i, (((![1, 1, 12, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 630 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 12^2 + 22^2 = 630
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_11_10

theorem weighted_01_00_11_10 : b4RawGapContribution ![1, 0, 11, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 11, 10] = b4GapPatternWeight 0 11 10 * 0 :=
      b4GapContribution_from_row 1 0 11 10 0 row_01_00_11_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_11_10

theorem row_01_00_11_11 : b4RowContribution (![1, 1, 12, 23] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 1, 12, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 1 + 12 + 23 = 37
    decide
  have hzsq : (∑ i, (((![1, 1, 12, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 675 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 1^2 + 12^2 + 23^2 = 675
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_00_11_11

theorem weighted_01_00_11_11 : b4RawGapContribution ![1, 0, 11, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 0, 11, 11] = b4GapPatternWeight 0 11 11 * 0 :=
      b4GapContribution_from_row 1 0 11 11 0 row_01_00_11_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_00_11_11

def dvalues_01_00_11 : Fin 12 → ℕ := ![192, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_00_11

theorem dblock_01_00_11 : b4GapPatternDBlock 1 0 11 = 192 := by
  calc
    b4GapPatternDBlock 1 0 11 = ∑ d : Fin 12, dvalues_01_00_11 d := by
      apply b4GapDBlock_of_rows 1 0 11 dvalues_01_00_11
      intro d
      fin_cases d
      · exact weighted_01_00_11_00
      · exact weighted_01_00_11_01
      · exact weighted_01_00_11_02
      · exact weighted_01_00_11_03
      · exact weighted_01_00_11_04
      · exact weighted_01_00_11_05
      · exact weighted_01_00_11_06
      · exact weighted_01_00_11_07
      · exact weighted_01_00_11_08
      · exact weighted_01_00_11_09
      · exact weighted_01_00_11_10
      · exact weighted_01_00_11_11
    _ = 192 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_00_11

end Paper7MomentGapNumeric
