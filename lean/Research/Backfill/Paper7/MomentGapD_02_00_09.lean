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

theorem row_02_00_09_00 : b4RowContribution (![2, 2, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 11, 11] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 11 + 11 = 26
    decide
  have hzsq : (∑ i, (((![2, 2, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 250 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 11^2 + 11^2 = 250
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_09_00

theorem weighted_02_00_09_00 : b4RawGapContribution ![2, 0, 9, 0] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 9, 0] = b4GapPatternWeight 0 9 0 * 0 :=
      b4GapContribution_from_row 2 0 9 0 0 row_02_00_09_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_09_00

def layers_02_00_09_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 8, 9, 9, 9, 9, 9, 9, 9, 9, 8, 6, 3, 1, 0, 0, 0], ![1, 4, 10, 18, 27, 36, 45, 54, 63, 72, 81, 90, 98, 103, 103, 98, 90, 81, 72]]
#print axioms Paper7MomentGapNumeric.layers_02_00_09_01

theorem cells_02_00_09_01 : QTableValid (![2, 2, 11, 12] : Fin 4 → ℕ) layers_02_00_09_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_02_00_09_01

theorem valid_02_00_09_01 :
    SparseRowValid (![2, 2, 11, 12] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_02_00_09_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![2, 2, 11, 12] : Fin 4 → ℕ) i) = 27 := by
      rw [Fin.sum_univ_four]
      change 2 + 2 + 11 + 12 = 27
      decide
    have hzsq : (∑ i, (((![2, 2, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 273 := by
      rw [Fin.sum_univ_four]
      change (2 : ℤ)^2 + 2^2 + 11^2 + 12^2 = 273
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_02_00_09_01
#print axioms Paper7MomentGapNumeric.valid_02_00_09_01

def qvalues_02_00_09_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_02_00_09_01

theorem row_02_00_09_01 : b4RowContribution (![2, 2, 11, 12] : Fin 4 → ℕ) = 72 := by
  calc
    b4RowContribution (![2, 2, 11, 12] : Fin 4 → ℕ) =
        sparseRowValue ({9} : Finset (Fin 19)) (fun _ => layers_02_00_09_01) :=
      sparseRow_sound (![2, 2, 11, 12] : Fin 4 → ℕ) ({9} : Finset (Fin 19)) (fun _ => layers_02_00_09_01) valid_02_00_09_01
    _ = 72 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_02_00_09_01 Q := by
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
        _ = 72 := by decide
#print axioms Paper7MomentGapNumeric.row_02_00_09_01

theorem weighted_02_00_09_01 : b4RawGapContribution ![2, 0, 9, 1] = 864 := by
  calc
    b4RawGapContribution ![2, 0, 9, 1] = b4GapPatternWeight 0 9 1 * 72 :=
      b4GapContribution_from_row 2 0 9 1 72 row_02_00_09_01
    _ = 864 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_09_01

theorem row_02_00_09_02 : b4RowContribution (![2, 2, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 11, 13] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 11 + 13 = 28
    decide
  have hzsq : (∑ i, (((![2, 2, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 298 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 11^2 + 13^2 = 298
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_09_02

theorem weighted_02_00_09_02 : b4RawGapContribution ![2, 0, 9, 2] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 9, 2] = b4GapPatternWeight 0 9 2 * 0 :=
      b4GapContribution_from_row 2 0 9 2 0 row_02_00_09_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_09_02

theorem row_02_00_09_03 : b4RowContribution (![2, 2, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 11, 14] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 11 + 14 = 29
    decide
  have hzsq : (∑ i, (((![2, 2, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 11^2 + 14^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_09_03

theorem weighted_02_00_09_03 : b4RawGapContribution ![2, 0, 9, 3] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 9, 3] = b4GapPatternWeight 0 9 3 * 0 :=
      b4GapContribution_from_row 2 0 9 3 0 row_02_00_09_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_09_03

theorem row_02_00_09_04 : b4RowContribution (![2, 2, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 11, 15] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 11 + 15 = 30
    decide
  have hzsq : (∑ i, (((![2, 2, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 354 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 11^2 + 15^2 = 354
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_09_04

theorem weighted_02_00_09_04 : b4RawGapContribution ![2, 0, 9, 4] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 9, 4] = b4GapPatternWeight 0 9 4 * 0 :=
      b4GapContribution_from_row 2 0 9 4 0 row_02_00_09_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_09_04

theorem row_02_00_09_05 : b4RowContribution (![2, 2, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 11, 16] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 11 + 16 = 31
    decide
  have hzsq : (∑ i, (((![2, 2, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 385 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 11^2 + 16^2 = 385
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_09_05

theorem weighted_02_00_09_05 : b4RawGapContribution ![2, 0, 9, 5] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 9, 5] = b4GapPatternWeight 0 9 5 * 0 :=
      b4GapContribution_from_row 2 0 9 5 0 row_02_00_09_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_09_05

theorem row_02_00_09_06 : b4RowContribution (![2, 2, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 11, 17] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 11 + 17 = 32
    decide
  have hzsq : (∑ i, (((![2, 2, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 418 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 11^2 + 17^2 = 418
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_09_06

theorem weighted_02_00_09_06 : b4RawGapContribution ![2, 0, 9, 6] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 9, 6] = b4GapPatternWeight 0 9 6 * 0 :=
      b4GapContribution_from_row 2 0 9 6 0 row_02_00_09_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_09_06

theorem row_02_00_09_07 : b4RowContribution (![2, 2, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 11, 18] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 11 + 18 = 33
    decide
  have hzsq : (∑ i, (((![2, 2, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 453 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 11^2 + 18^2 = 453
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_09_07

theorem weighted_02_00_09_07 : b4RawGapContribution ![2, 0, 9, 7] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 9, 7] = b4GapPatternWeight 0 9 7 * 0 :=
      b4GapContribution_from_row 2 0 9 7 0 row_02_00_09_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_09_07

theorem row_02_00_09_08 : b4RowContribution (![2, 2, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 11, 19] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 11 + 19 = 34
    decide
  have hzsq : (∑ i, (((![2, 2, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 490 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 11^2 + 19^2 = 490
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_09_08

theorem weighted_02_00_09_08 : b4RawGapContribution ![2, 0, 9, 8] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 9, 8] = b4GapPatternWeight 0 9 8 * 0 :=
      b4GapContribution_from_row 2 0 9 8 0 row_02_00_09_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_09_08

theorem row_02_00_09_09 : b4RowContribution (![2, 2, 11, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 11, 20] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 11 + 20 = 35
    decide
  have hzsq : (∑ i, (((![2, 2, 11, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 529 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 11^2 + 20^2 = 529
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_09_09

theorem weighted_02_00_09_09 : b4RawGapContribution ![2, 0, 9, 9] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 9, 9] = b4GapPatternWeight 0 9 9 * 0 :=
      b4GapContribution_from_row 2 0 9 9 0 row_02_00_09_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_09_09

theorem row_02_00_09_10 : b4RowContribution (![2, 2, 11, 21] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 11, 21] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 11 + 21 = 36
    decide
  have hzsq : (∑ i, (((![2, 2, 11, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 570 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 11^2 + 21^2 = 570
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_09_10

theorem weighted_02_00_09_10 : b4RawGapContribution ![2, 0, 9, 10] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 9, 10] = b4GapPatternWeight 0 9 10 * 0 :=
      b4GapContribution_from_row 2 0 9 10 0 row_02_00_09_10
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_09_10

theorem row_02_00_09_11 : b4RowContribution (![2, 2, 11, 22] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![2, 2, 11, 22] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 2 + 2 + 11 + 22 = 37
    decide
  have hzsq : (∑ i, (((![2, 2, 11, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 613 := by
    rw [Fin.sum_univ_four]
    change (2 : ℤ)^2 + 2^2 + 11^2 + 22^2 = 613
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_02_00_09_11

theorem weighted_02_00_09_11 : b4RawGapContribution ![2, 0, 9, 11] = 0 := by
  calc
    b4RawGapContribution ![2, 0, 9, 11] = b4GapPatternWeight 0 9 11 * 0 :=
      b4GapContribution_from_row 2 0 9 11 0 row_02_00_09_11
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_02_00_09_11

def dvalues_02_00_09 : Fin 12 → ℕ := ![0, 864, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_02_00_09

theorem dblock_02_00_09 : b4GapPatternDBlock 2 0 9 = 864 := by
  calc
    b4GapPatternDBlock 2 0 9 = ∑ d : Fin 12, dvalues_02_00_09 d := by
      apply b4GapDBlock_of_rows 2 0 9 dvalues_02_00_09
      intro d
      fin_cases d
      · exact weighted_02_00_09_00
      · exact weighted_02_00_09_01
      · exact weighted_02_00_09_02
      · exact weighted_02_00_09_03
      · exact weighted_02_00_09_04
      · exact weighted_02_00_09_05
      · exact weighted_02_00_09_06
      · exact weighted_02_00_09_07
      · exact weighted_02_00_09_08
      · exact weighted_02_00_09_09
      · exact weighted_02_00_09_10
      · exact weighted_02_00_09_11
    _ = 864 := by decide
#print axioms Paper7MomentGapNumeric.dblock_02_00_09

end Paper7MomentGapNumeric
