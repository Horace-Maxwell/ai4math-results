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

theorem row_01_02_08_00 : b4RowContribution (![1, 3, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 11, 11] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 11 + 11 = 26
    decide
  have hzsq : (∑ i, (((![1, 3, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 252 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 11^2 + 11^2 = 252
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_08_00

theorem weighted_01_02_08_00 : b4RawGapContribution ![1, 2, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 8, 0] = b4GapPatternWeight 2 8 0 * 0 :=
      b4GapContribution_from_row 1 2 8 0 0 row_01_02_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_08_00

def layers_01_02_08_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 5, 7, 8, 8, 8, 8, 8, 8, 8, 8, 7, 5, 3, 1, 0, 0, 0], ![1, 4, 9, 16, 24, 32, 40, 48, 56, 64, 72, 80, 87, 91, 91, 87, 80, 72, 64]]
#print axioms Paper7MomentGapNumeric.layers_01_02_08_01

theorem cells_01_02_08_01 : QTableValid (![1, 3, 11, 12] : Fin 4 → ℕ) layers_01_02_08_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_01_02_08_01

theorem valid_01_02_08_01 :
    SparseRowValid (![1, 3, 11, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_01_02_08_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![1, 3, 11, 12] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 1 + 3 + 11 + 12 = 27
      decide
    have hzsq : (∑ i, (((![1, 3, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 275 := by
      rw [Fin.sum_univ_four]
      change (1 : ℤ)^2 + 3^2 + 11^2 + 12^2 = 275
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_02_08_01
#print axioms Paper7MomentGapNumeric.valid_01_02_08_01

def qvalues_01_02_08_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_01_02_08_01

theorem row_01_02_08_01 : b4RowContribution (![1, 3, 11, 12] : Fin 4 → ℕ) = 56 := by
  calc
    b4RowContribution (![1, 3, 11, 12] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_01_02_08_01) :=
      sparseRow_sound (![1, 3, 11, 12] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_01_02_08_01) valid_01_02_08_01
    _ = 56 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_02_08_01 Q := by
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
        _ = 56 := by decide
#print axioms Paper7MomentGapNumeric.row_01_02_08_01

theorem weighted_01_02_08_01 : b4RawGapContribution ![1, 2, 8, 1] = 1344 := by
  calc
    b4RawGapContribution ![1, 2, 8, 1] = b4GapPatternWeight 2 8 1 * 56 :=
      b4GapContribution_from_row 1 2 8 1 56 row_01_02_08_01
    _ = 1344 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_08_01

theorem row_01_02_08_02 : b4RowContribution (![1, 3, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 11, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 11 + 13 = 28
    decide
  have hzsq : (∑ i, (((![1, 3, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 300 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 11^2 + 13^2 = 300
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_08_02

theorem weighted_01_02_08_02 : b4RawGapContribution ![1, 2, 8, 2] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 8, 2] = b4GapPatternWeight 2 8 2 * 0 :=
      b4GapContribution_from_row 1 2 8 2 0 row_01_02_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_08_02

theorem row_01_02_08_03 : b4RowContribution (![1, 3, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 11, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 11 + 14 = 29
    decide
  have hzsq : (∑ i, (((![1, 3, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 327 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 11^2 + 14^2 = 327
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_08_03

theorem weighted_01_02_08_03 : b4RawGapContribution ![1, 2, 8, 3] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 8, 3] = b4GapPatternWeight 2 8 3 * 0 :=
      b4GapContribution_from_row 1 2 8 3 0 row_01_02_08_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_08_03

theorem row_01_02_08_04 : b4RowContribution (![1, 3, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 11, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 11 + 15 = 30
    decide
  have hzsq : (∑ i, (((![1, 3, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 356 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 11^2 + 15^2 = 356
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_08_04

theorem weighted_01_02_08_04 : b4RawGapContribution ![1, 2, 8, 4] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 8, 4] = b4GapPatternWeight 2 8 4 * 0 :=
      b4GapContribution_from_row 1 2 8 4 0 row_01_02_08_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_08_04

theorem row_01_02_08_05 : b4RowContribution (![1, 3, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 11, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 11 + 16 = 31
    decide
  have hzsq : (∑ i, (((![1, 3, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 387 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 11^2 + 16^2 = 387
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_08_05

theorem weighted_01_02_08_05 : b4RawGapContribution ![1, 2, 8, 5] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 8, 5] = b4GapPatternWeight 2 8 5 * 0 :=
      b4GapContribution_from_row 1 2 8 5 0 row_01_02_08_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_08_05

theorem row_01_02_08_06 : b4RowContribution (![1, 3, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 11, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 11 + 17 = 32
    decide
  have hzsq : (∑ i, (((![1, 3, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 420 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 11^2 + 17^2 = 420
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_08_06

theorem weighted_01_02_08_06 : b4RawGapContribution ![1, 2, 8, 6] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 8, 6] = b4GapPatternWeight 2 8 6 * 0 :=
      b4GapContribution_from_row 1 2 8 6 0 row_01_02_08_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_08_06

theorem row_01_02_08_07 : b4RowContribution (![1, 3, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 11, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 11 + 18 = 33
    decide
  have hzsq : (∑ i, (((![1, 3, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 455 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 11^2 + 18^2 = 455
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_08_07

theorem weighted_01_02_08_07 : b4RawGapContribution ![1, 2, 8, 7] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 8, 7] = b4GapPatternWeight 2 8 7 * 0 :=
      b4GapContribution_from_row 1 2 8 7 0 row_01_02_08_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_08_07

theorem row_01_02_08_08 : b4RowContribution (![1, 3, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 11, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 11 + 19 = 34
    decide
  have hzsq : (∑ i, (((![1, 3, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 492 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 11^2 + 19^2 = 492
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_08_08

theorem weighted_01_02_08_08 : b4RawGapContribution ![1, 2, 8, 8] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 8, 8] = b4GapPatternWeight 2 8 8 * 0 :=
      b4GapContribution_from_row 1 2 8 8 0 row_01_02_08_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_08_08

theorem row_01_02_08_09 : b4RowContribution (![1, 3, 11, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 11, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 11 + 20 = 35
    decide
  have hzsq : (∑ i, (((![1, 3, 11, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 531 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 11^2 + 20^2 = 531
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_08_09

theorem weighted_01_02_08_09 : b4RawGapContribution ![1, 2, 8, 9] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 8, 9] = b4GapPatternWeight 2 8 9 * 0 :=
      b4GapContribution_from_row 1 2 8 9 0 row_01_02_08_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_08_09

theorem row_01_02_08_10 : b4RowContribution (![1, 3, 11, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 11, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 11 + 21 = 36
    decide
  have hzsq : (∑ i, (((![1, 3, 11, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 572 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 11^2 + 21^2 = 572
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_08_10

theorem weighted_01_02_08_10 : b4RawGapContribution ![1, 2, 8, 10] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 8, 10] = b4GapPatternWeight 2 8 10 * 0 :=
      b4GapContribution_from_row 1 2 8 10 0 row_01_02_08_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_08_10

theorem row_01_02_08_11 : b4RowContribution (![1, 3, 11, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![1, 3, 11, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 1 + 3 + 11 + 22 = 37
    decide
  have hzsq : (∑ i, (((![1, 3, 11, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 615 := by
    rw [Fin.sum_univ_four]
    change (1 : ℤ)^2 + 3^2 + 11^2 + 22^2 = 615
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_01_02_08_11

theorem weighted_01_02_08_11 : b4RawGapContribution ![1, 2, 8, 11] = 0 := by
  calc
    b4RawGapContribution ![1, 2, 8, 11] = b4GapPatternWeight 2 8 11 * 0 :=
      b4GapContribution_from_row 1 2 8 11 0 row_01_02_08_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_01_02_08_11

def dvalues_01_02_08 : Fin 12 → ℕ := ![0, 1344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_01_02_08

theorem dblock_01_02_08 : b4GapPatternDBlock 1 2 8 = 1344 := by
  calc
    b4GapPatternDBlock 1 2 8 = ∑ d : Fin 12, dvalues_01_02_08 d := by
      apply b4GapDBlock_of_rows 1 2 8 dvalues_01_02_08
      intro d
      fin_cases d
      · exact weighted_01_02_08_00
      · exact weighted_01_02_08_01
      · exact weighted_01_02_08_02
      · exact weighted_01_02_08_03
      · exact weighted_01_02_08_04
      · exact weighted_01_02_08_05
      · exact weighted_01_02_08_06
      · exact weighted_01_02_08_07
      · exact weighted_01_02_08_08
      · exact weighted_01_02_08_09
      · exact weighted_01_02_08_10
      · exact weighted_01_02_08_11
    _ = 1344 := by decide
#print axioms Paper7MomentGapNumeric.dblock_01_02_08

end Paper7MomentGapNumeric
