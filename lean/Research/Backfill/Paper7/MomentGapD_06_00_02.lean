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

theorem row_06_00_02_00 : b4RowContribution (![6, 6, 8, 8] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 8, 8] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 8 + 8 = 28
    decide
  have hzsq : (∑ i, (((![6, 6, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 200 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 8^2 + 8^2 = 200
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_02_00

theorem weighted_06_00_02_00 : b4RawGapContribution ![6, 0, 2, 0] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 2, 0] = b4GapPatternWeight 0 2 0 * 0 :=
      b4GapContribution_from_row 6 0 2 0 0 row_06_00_02_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_02_00

theorem row_06_00_02_01 : b4RowContribution (![6, 6, 8, 9] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 8, 9] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 8 + 9 = 29
    decide
  have hzsq : (∑ i, (((![6, 6, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 217 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 8^2 + 9^2 = 217
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_02_01

theorem weighted_06_00_02_01 : b4RawGapContribution ![6, 0, 2, 1] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 2, 1] = b4GapPatternWeight 0 2 1 * 0 :=
      b4GapContribution_from_row 6 0 2 1 0 row_06_00_02_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_02_01

theorem row_06_00_02_02 : b4RowContribution (![6, 6, 8, 10] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 8, 10] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 8 + 10 = 30
    decide
  have hzsq : (∑ i, (((![6, 6, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 236 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 8^2 + 10^2 = 236
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_02_02

theorem weighted_06_00_02_02 : b4RawGapContribution ![6, 0, 2, 2] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 2, 2] = b4GapPatternWeight 0 2 2 * 0 :=
      b4GapContribution_from_row 6 0 2 2 0 row_06_00_02_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_02_02

theorem row_06_00_02_03 : b4RowContribution (![6, 6, 8, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 8, 11] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 8 + 11 = 31
    decide
  have hzsq : (∑ i, (((![6, 6, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 257 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 8^2 + 11^2 = 257
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_02_03

theorem weighted_06_00_02_03 : b4RawGapContribution ![6, 0, 2, 3] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 2, 3] = b4GapPatternWeight 0 2 3 * 0 :=
      b4GapContribution_from_row 6 0 2 3 0 row_06_00_02_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_02_03

def layers_06_00_02_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 21, 28, 34, 39, 42, 43, 42, 39, 34, 28, 21, 15, 10, 6], ![1, 4, 10, 20, 35, 56, 84, 118, 157, 199, 242, 284, 323, 356, 381, 396, 401, 396, 381]]
#print axioms Paper7MomentGapNumeric.layers_06_00_02_04

theorem cells_06_00_02_04 : QTableValid (![6, 6, 8, 12] : Fin 4 → ℕ) layers_06_00_02_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_06_00_02_04

theorem valid_06_00_02_04 :
    SparseRowValid (![6, 6, 8, 12] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_06_00_02_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![6, 6, 8, 12] : Fin 4 → ℕ) i) = 32 := by
      rw [Fin.sum_univ_four]
      change 6 + 6 + 8 + 12 = 32
      decide
    have hzsq : (∑ i, (((![6, 6, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 280 := by
      rw [Fin.sum_univ_four]
      change (6 : ℤ)^2 + 6^2 + 8^2 + 12^2 = 280
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_06_00_02_04
#print axioms Paper7MomentGapNumeric.valid_06_00_02_04

def qvalues_06_00_02_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_06_00_02_04

theorem row_06_00_02_04 : b4RowContribution (![6, 6, 8, 12] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![6, 6, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_06_00_02_04) :=
      sparseRow_sound (![6, 6, 8, 12] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_06_00_02_04) valid_06_00_02_04
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_06_00_02_04 Q := by
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
#print axioms Paper7MomentGapNumeric.row_06_00_02_04

theorem weighted_06_00_02_04 : b4RawGapContribution ![6, 0, 2, 4] = 420 := by
  calc
    b4RawGapContribution ![6, 0, 2, 4] = b4GapPatternWeight 0 2 4 * 35 :=
      b4GapContribution_from_row 6 0 2 4 35 row_06_00_02_04
    _ = 420 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_02_04

theorem row_06_00_02_05 : b4RowContribution (![6, 6, 8, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 8, 13] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 8 + 13 = 33
    decide
  have hzsq : (∑ i, (((![6, 6, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 305 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 8^2 + 13^2 = 305
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_02_05

theorem weighted_06_00_02_05 : b4RawGapContribution ![6, 0, 2, 5] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 2, 5] = b4GapPatternWeight 0 2 5 * 0 :=
      b4GapContribution_from_row 6 0 2 5 0 row_06_00_02_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_02_05

theorem row_06_00_02_06 : b4RowContribution (![6, 6, 8, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 8, 14] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 8 + 14 = 34
    decide
  have hzsq : (∑ i, (((![6, 6, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 332 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 8^2 + 14^2 = 332
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_02_06

theorem weighted_06_00_02_06 : b4RawGapContribution ![6, 0, 2, 6] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 2, 6] = b4GapPatternWeight 0 2 6 * 0 :=
      b4GapContribution_from_row 6 0 2 6 0 row_06_00_02_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_02_06

theorem row_06_00_02_07 : b4RowContribution (![6, 6, 8, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 8, 15] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 8 + 15 = 35
    decide
  have hzsq : (∑ i, (((![6, 6, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 361 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 8^2 + 15^2 = 361
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_02_07

theorem weighted_06_00_02_07 : b4RawGapContribution ![6, 0, 2, 7] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 2, 7] = b4GapPatternWeight 0 2 7 * 0 :=
      b4GapContribution_from_row 6 0 2 7 0 row_06_00_02_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_02_07

theorem row_06_00_02_08 : b4RowContribution (![6, 6, 8, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 8, 16] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 8 + 16 = 36
    decide
  have hzsq : (∑ i, (((![6, 6, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 392 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 8^2 + 16^2 = 392
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_02_08

theorem weighted_06_00_02_08 : b4RawGapContribution ![6, 0, 2, 8] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 2, 8] = b4GapPatternWeight 0 2 8 * 0 :=
      b4GapContribution_from_row 6 0 2 8 0 row_06_00_02_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_02_08

theorem row_06_00_02_09 : b4RowContribution (![6, 6, 8, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![6, 6, 8, 17] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 6 + 6 + 8 + 17 = 37
    decide
  have hzsq : (∑ i, (((![6, 6, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 425 := by
    rw [Fin.sum_univ_four]
    change (6 : ℤ)^2 + 6^2 + 8^2 + 17^2 = 425
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_06_00_02_09

theorem weighted_06_00_02_09 : b4RawGapContribution ![6, 0, 2, 9] = 0 := by
  calc
    b4RawGapContribution ![6, 0, 2, 9] = b4GapPatternWeight 0 2 9 * 0 :=
      b4GapContribution_from_row 6 0 2 9 0 row_06_00_02_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_06_00_02_09

def dvalues_06_00_02 : Fin 10 → ℕ := ![0, 0, 0, 0, 420, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_06_00_02

theorem dblock_06_00_02 : b4GapPatternDBlock 6 0 2 = 420 := by
  calc
    b4GapPatternDBlock 6 0 2 = ∑ d : Fin 10, dvalues_06_00_02 d := by
      apply b4GapDBlock_of_rows 6 0 2 dvalues_06_00_02
      intro d
      fin_cases d
      · exact weighted_06_00_02_00
      · exact weighted_06_00_02_01
      · exact weighted_06_00_02_02
      · exact weighted_06_00_02_03
      · exact weighted_06_00_02_04
      · exact weighted_06_00_02_05
      · exact weighted_06_00_02_06
      · exact weighted_06_00_02_07
      · exact weighted_06_00_02_08
      · exact weighted_06_00_02_09
    _ = 420 := by decide
#print axioms Paper7MomentGapNumeric.dblock_06_00_02

end Paper7MomentGapNumeric
