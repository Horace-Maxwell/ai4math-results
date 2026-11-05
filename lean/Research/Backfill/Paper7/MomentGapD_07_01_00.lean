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

theorem row_07_01_00_00 : b4RowContribution (![7, 8, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 8, 8, 8] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 7 + 8 + 8 + 8 = 31
    decide
  have hzsq : (∑ i, (((![7, 8, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 241 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 8^2 + 8^2 + 8^2 = 241
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_01_00_00

theorem weighted_07_01_00_00 : b4RawGapContribution ![7, 1, 0, 0] = 0 := by
  calc
    b4RawGapContribution ![7, 1, 0, 0] = b4GapPatternWeight 1 0 0 * 0 :=
      b4GapContribution_from_row 7 1 0 0 0 row_07_01_00_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_01_00_00

theorem row_07_01_00_01 : b4RowContribution (![7, 8, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 8, 8, 9] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 7 + 8 + 8 + 9 = 32
    decide
  have hzsq : (∑ i, (((![7, 8, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 258 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 8^2 + 8^2 + 9^2 = 258
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_01_00_01

theorem weighted_07_01_00_01 : b4RawGapContribution ![7, 1, 0, 1] = 0 := by
  calc
    b4RawGapContribution ![7, 1, 0, 1] = b4GapPatternWeight 1 0 1 * 0 :=
      b4GapContribution_from_row 7 1 0 1 0 row_07_01_00_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_01_00_01

def layers_07_01_00_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 8, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 36, 44, 50, 54, 56, 56, 54, 50, 44, 36, 28, 21], ![1, 4, 10, 20, 35, 56, 84, 120, 164, 214, 268, 323, 376, 424, 464, 493, 508, 508, 493]]
#print axioms Paper7MomentGapNumeric.layers_07_01_00_02

theorem cells_07_01_00_02 : QTableValid (![7, 8, 8, 10] : Fin 4 → ℕ) layers_07_01_00_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_07_01_00_02

theorem valid_07_01_00_02 :
    SparseRowValid (![7, 8, 8, 10] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_07_01_00_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![7, 8, 8, 10] : Fin 4 → ℕ) i) = 33 := by
      rw [Fin.sum_univ_four]
      change 7 + 8 + 8 + 10 = 33
      decide
    have hzsq : (∑ i, (((![7, 8, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 277 := by
      rw [Fin.sum_univ_four]
      change (7 : ℤ)^2 + 8^2 + 8^2 + 10^2 = 277
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_07_01_00_02
#print axioms Paper7MomentGapNumeric.valid_07_01_00_02

def qvalues_07_01_00_02 : Fin 19 → ℕ := ![0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_07_01_00_02

theorem row_07_01_00_02 : b4RowContribution (![7, 8, 8, 10] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![7, 8, 8, 10] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_07_01_00_02) :=
      sparseRow_sound (![7, 8, 8, 10] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_07_01_00_02) valid_07_01_00_02
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_07_01_00_02 Q := by
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
#print axioms Paper7MomentGapNumeric.row_07_01_00_02

theorem weighted_07_01_00_02 : b4RawGapContribution ![7, 1, 0, 2] = 420 := by
  calc
    b4RawGapContribution ![7, 1, 0, 2] = b4GapPatternWeight 1 0 2 * 35 :=
      b4GapContribution_from_row 7 1 0 2 35 row_07_01_00_02
    _ = 420 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_01_00_02

theorem row_07_01_00_03 : b4RowContribution (![7, 8, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 8, 8, 11] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 7 + 8 + 8 + 11 = 34
    decide
  have hzsq : (∑ i, (((![7, 8, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 298 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 8^2 + 8^2 + 11^2 = 298
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_01_00_03

theorem weighted_07_01_00_03 : b4RawGapContribution ![7, 1, 0, 3] = 0 := by
  calc
    b4RawGapContribution ![7, 1, 0, 3] = b4GapPatternWeight 1 0 3 * 0 :=
      b4GapContribution_from_row 7 1 0 3 0 row_07_01_00_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_01_00_03

theorem row_07_01_00_04 : b4RowContribution (![7, 8, 8, 12] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 8, 8, 12] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 7 + 8 + 8 + 12 = 35
    decide
  have hzsq : (∑ i, (((![7, 8, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 321 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 8^2 + 8^2 + 12^2 = 321
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_01_00_04

theorem weighted_07_01_00_04 : b4RawGapContribution ![7, 1, 0, 4] = 0 := by
  calc
    b4RawGapContribution ![7, 1, 0, 4] = b4GapPatternWeight 1 0 4 * 0 :=
      b4GapContribution_from_row 7 1 0 4 0 row_07_01_00_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_01_00_04

theorem row_07_01_00_05 : b4RowContribution (![7, 8, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 8, 8, 13] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 7 + 8 + 8 + 13 = 36
    decide
  have hzsq : (∑ i, (((![7, 8, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 346 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 8^2 + 8^2 + 13^2 = 346
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_01_00_05

theorem weighted_07_01_00_05 : b4RawGapContribution ![7, 1, 0, 5] = 0 := by
  calc
    b4RawGapContribution ![7, 1, 0, 5] = b4GapPatternWeight 1 0 5 * 0 :=
      b4GapContribution_from_row 7 1 0 5 0 row_07_01_00_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_01_00_05

theorem row_07_01_00_06 : b4RowContribution (![7, 8, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![7, 8, 8, 14] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 7 + 8 + 8 + 14 = 37
    decide
  have hzsq : (∑ i, (((![7, 8, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 373 := by
    rw [Fin.sum_univ_four]
    change (7 : ℤ)^2 + 8^2 + 8^2 + 14^2 = 373
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_07_01_00_06

theorem weighted_07_01_00_06 : b4RawGapContribution ![7, 1, 0, 6] = 0 := by
  calc
    b4RawGapContribution ![7, 1, 0, 6] = b4GapPatternWeight 1 0 6 * 0 :=
      b4GapContribution_from_row 7 1 0 6 0 row_07_01_00_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_07_01_00_06

def dvalues_07_01_00 : Fin 7 → ℕ := ![0, 0, 420, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_07_01_00

theorem dblock_07_01_00 : b4GapPatternDBlock 7 1 0 = 420 := by
  calc
    b4GapPatternDBlock 7 1 0 = ∑ d : Fin 7, dvalues_07_01_00 d := by
      apply b4GapDBlock_of_rows 7 1 0 dvalues_07_01_00
      intro d
      fin_cases d
      · exact weighted_07_01_00_00
      · exact weighted_07_01_00_01
      · exact weighted_07_01_00_02
      · exact weighted_07_01_00_03
      · exact weighted_07_01_00_04
      · exact weighted_07_01_00_05
      · exact weighted_07_01_00_06
    _ = 420 := by decide
#print axioms Paper7MomentGapNumeric.dblock_07_01_00

end Paper7MomentGapNumeric
