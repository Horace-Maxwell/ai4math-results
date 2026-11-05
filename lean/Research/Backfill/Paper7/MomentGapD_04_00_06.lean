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

def layers_04_00_06_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 19, 22, 24, 25, 25, 25, 24, 22, 19, 15, 10, 6, 3, 1], ![1, 4, 10, 20, 35, 54, 76, 100, 125, 150, 175, 198, 217, 230, 235, 230, 217, 198, 175]]
#print axioms Paper7MomentGapNumeric.layers_04_00_06_00

theorem cells_04_00_06_00 : QTableValid (![4, 4, 10, 10] : Fin 4 → ℕ) layers_04_00_06_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_00_06_00

theorem valid_04_00_06_00 :
    SparseRowValid (![4, 4, 10, 10] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_04_00_06_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 4, 10, 10] : Fin 4 → ℕ) i) = 28 := by
      rw [Fin.sum_univ_four]
      change 4 + 4 + 10 + 10 = 28
      decide
    have hzsq : (∑ i, (((![4, 4, 10, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 232 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 4^2 + 10^2 + 10^2 = 232
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_00_06_00
#print axioms Paper7MomentGapNumeric.valid_04_00_06_00

def qvalues_04_00_06_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_00_06_00

theorem row_04_00_06_00 : b4RowContribution (![4, 4, 10, 10] : Fin 4 → ℕ) = 35 := by
  calc
    b4RowContribution (![4, 4, 10, 10] : Fin 4 → ℕ) =
        sparseRowValue ({4} : Finset (Fin 19)) (fun _ => layers_04_00_06_00) :=
      sparseRow_sound (![4, 4, 10, 10] : Fin 4 → ℕ) ({4} : Finset (Fin 19)) (fun _ => layers_04_00_06_00) valid_04_00_06_00
    _ = 35 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_00_06_00 Q := by
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
#print axioms Paper7MomentGapNumeric.row_04_00_06_00

theorem weighted_04_00_06_00 : b4RawGapContribution ![4, 0, 6, 0] = 210 := by
  calc
    b4RawGapContribution ![4, 0, 6, 0] = b4GapPatternWeight 0 6 0 * 35 :=
      b4GapContribution_from_row 4 0 6 0 35 row_04_00_06_00
    _ = 210 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_06_00

theorem row_04_00_06_01 : b4RowContribution (![4, 4, 10, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 10, 11] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 10 + 11 = 29
    decide
  have hzsq : (∑ i, (((![4, 4, 10, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 253 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 10^2 + 11^2 = 253
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_06_01

theorem weighted_04_00_06_01 : b4RawGapContribution ![4, 0, 6, 1] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 6, 1] = b4GapPatternWeight 0 6 1 * 0 :=
      b4GapContribution_from_row 4 0 6 1 0 row_04_00_06_01
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_06_01

def layers_04_00_06_02 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 15, 19, 22, 24, 25, 25, 25, 24, 22, 19, 15, 10, 6, 3, 1], ![1, 4, 10, 20, 35, 54, 76, 100, 125, 150, 175, 199, 221, 239, 251, 255, 251, 239, 221]]
#print axioms Paper7MomentGapNumeric.layers_04_00_06_02

theorem cells_04_00_06_02 : QTableValid (![4, 4, 10, 12] : Fin 4 → ℕ) layers_04_00_06_02 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_04_00_06_02

theorem valid_04_00_06_02 :
    SparseRowValid (![4, 4, 10, 12] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_04_00_06_02) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![4, 4, 10, 12] : Fin 4 → ℕ) i) = 30 := by
      rw [Fin.sum_univ_four]
      change 4 + 4 + 10 + 12 = 30
      decide
    have hzsq : (∑ i, (((![4, 4, 10, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 276 := by
      rw [Fin.sum_univ_four]
      change (4 : ℤ)^2 + 4^2 + 10^2 + 12^2 = 276
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_04_00_06_02
#print axioms Paper7MomentGapNumeric.valid_04_00_06_02

def qvalues_04_00_06_02 : Fin 19 → ℕ := ![0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_04_00_06_02

theorem row_04_00_06_02 : b4RowContribution (![4, 4, 10, 12] : Fin 4 → ℕ) = 20 := by
  calc
    b4RowContribution (![4, 4, 10, 12] : Fin 4 → ℕ) =
        sparseRowValue ({3} : Finset (Fin 19)) (fun _ => layers_04_00_06_02) :=
      sparseRow_sound (![4, 4, 10, 12] : Fin 4 → ℕ) ({3} : Finset (Fin 19)) (fun _ => layers_04_00_06_02) valid_04_00_06_02
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_04_00_06_02 Q := by
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
#print axioms Paper7MomentGapNumeric.row_04_00_06_02

theorem weighted_04_00_06_02 : b4RawGapContribution ![4, 0, 6, 2] = 240 := by
  calc
    b4RawGapContribution ![4, 0, 6, 2] = b4GapPatternWeight 0 6 2 * 20 :=
      b4GapContribution_from_row 4 0 6 2 20 row_04_00_06_02
    _ = 240 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_06_02

theorem row_04_00_06_03 : b4RowContribution (![4, 4, 10, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 10, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 10 + 13 = 31
    decide
  have hzsq : (∑ i, (((![4, 4, 10, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 301 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 10^2 + 13^2 = 301
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_06_03

theorem weighted_04_00_06_03 : b4RawGapContribution ![4, 0, 6, 3] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 6, 3] = b4GapPatternWeight 0 6 3 * 0 :=
      b4GapContribution_from_row 4 0 6 3 0 row_04_00_06_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_06_03

theorem row_04_00_06_04 : b4RowContribution (![4, 4, 10, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 10, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 10 + 14 = 32
    decide
  have hzsq : (∑ i, (((![4, 4, 10, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 328 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 10^2 + 14^2 = 328
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_06_04

theorem weighted_04_00_06_04 : b4RawGapContribution ![4, 0, 6, 4] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 6, 4] = b4GapPatternWeight 0 6 4 * 0 :=
      b4GapContribution_from_row 4 0 6 4 0 row_04_00_06_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_06_04

theorem row_04_00_06_05 : b4RowContribution (![4, 4, 10, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 10, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 10 + 15 = 33
    decide
  have hzsq : (∑ i, (((![4, 4, 10, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 357 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 10^2 + 15^2 = 357
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_06_05

theorem weighted_04_00_06_05 : b4RawGapContribution ![4, 0, 6, 5] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 6, 5] = b4GapPatternWeight 0 6 5 * 0 :=
      b4GapContribution_from_row 4 0 6 5 0 row_04_00_06_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_06_05

theorem row_04_00_06_06 : b4RowContribution (![4, 4, 10, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 10, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 10 + 16 = 34
    decide
  have hzsq : (∑ i, (((![4, 4, 10, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 388 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 10^2 + 16^2 = 388
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_06_06

theorem weighted_04_00_06_06 : b4RawGapContribution ![4, 0, 6, 6] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 6, 6] = b4GapPatternWeight 0 6 6 * 0 :=
      b4GapContribution_from_row 4 0 6 6 0 row_04_00_06_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_06_06

theorem row_04_00_06_07 : b4RowContribution (![4, 4, 10, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 10, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 10 + 17 = 35
    decide
  have hzsq : (∑ i, (((![4, 4, 10, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 421 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 10^2 + 17^2 = 421
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_06_07

theorem weighted_04_00_06_07 : b4RawGapContribution ![4, 0, 6, 7] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 6, 7] = b4GapPatternWeight 0 6 7 * 0 :=
      b4GapContribution_from_row 4 0 6 7 0 row_04_00_06_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_06_07

theorem row_04_00_06_08 : b4RowContribution (![4, 4, 10, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 10, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 10 + 18 = 36
    decide
  have hzsq : (∑ i, (((![4, 4, 10, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 456 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 10^2 + 18^2 = 456
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_06_08

theorem weighted_04_00_06_08 : b4RawGapContribution ![4, 0, 6, 8] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 6, 8] = b4GapPatternWeight 0 6 8 * 0 :=
      b4GapContribution_from_row 4 0 6 8 0 row_04_00_06_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_06_08

theorem row_04_00_06_09 : b4RowContribution (![4, 4, 10, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![4, 4, 10, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 4 + 4 + 10 + 19 = 37
    decide
  have hzsq : (∑ i, (((![4, 4, 10, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 493 := by
    rw [Fin.sum_univ_four]
    change (4 : ℤ)^2 + 4^2 + 10^2 + 19^2 = 493
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_04_00_06_09

theorem weighted_04_00_06_09 : b4RawGapContribution ![4, 0, 6, 9] = 0 := by
  calc
    b4RawGapContribution ![4, 0, 6, 9] = b4GapPatternWeight 0 6 9 * 0 :=
      b4GapContribution_from_row 4 0 6 9 0 row_04_00_06_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_04_00_06_09

def dvalues_04_00_06 : Fin 10 → ℕ := ![210, 0, 240, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_04_00_06

theorem dblock_04_00_06 : b4GapPatternDBlock 4 0 6 = 450 := by
  calc
    b4GapPatternDBlock 4 0 6 = ∑ d : Fin 10, dvalues_04_00_06 d := by
      apply b4GapDBlock_of_rows 4 0 6 dvalues_04_00_06
      intro d
      fin_cases d
      · exact weighted_04_00_06_00
      · exact weighted_04_00_06_01
      · exact weighted_04_00_06_02
      · exact weighted_04_00_06_03
      · exact weighted_04_00_06_04
      · exact weighted_04_00_06_05
      · exact weighted_04_00_06_06
      · exact weighted_04_00_06_07
      · exact weighted_04_00_06_08
      · exact weighted_04_00_06_09
    _ = 450 := by decide
#print axioms Paper7MomentGapNumeric.dblock_04_00_06

end Paper7MomentGapNumeric
