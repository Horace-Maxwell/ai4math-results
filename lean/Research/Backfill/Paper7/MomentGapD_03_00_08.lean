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

theorem row_03_00_08_00 : b4RowContribution (![3, 3, 11, 11] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 11, 11] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 11 + 11 = 28
    decide
  have hzsq : (∑ i, (((![3, 3, 11, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 260 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 11^2 + 11^2 = 260
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_08_00

theorem weighted_03_00_08_00 : b4RawGapContribution ![3, 0, 8, 0] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 8, 0] = b4GapPatternWeight 0 8 0 * 0 :=
      b4GapContribution_from_row 3 0 8 0 0 row_03_00_08_00
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_08_00

def layers_03_00_08_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 6, 10, 13, 15, 16, 16, 16, 16, 16, 16, 15, 13, 10, 6, 3, 1, 0], ![1, 4, 10, 20, 33, 48, 64, 80, 96, 112, 128, 144, 159, 171, 178, 178, 171, 159, 144]]
#print axioms Paper7MomentGapNumeric.layers_03_00_08_01

theorem cells_03_00_08_01 : QTableValid (![3, 3, 11, 12] : Fin 4 → ℕ) layers_03_00_08_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentGapNumeric.cells_03_00_08_01

theorem valid_03_00_08_01 :
    SparseRowValid (![3, 3, 11, 12] : Fin 4 → ℕ) ({1, 7} : Finset (Fin 19)) (fun _ => layers_03_00_08_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![3, 3, 11, 12] : Fin 4 → ℕ) i) = 29 := by
      rw [Fin.sum_univ_four]
      change 3 + 3 + 11 + 12 = 29
      decide
    have hzsq : (∑ i, (((![3, 3, 11, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 283 := by
      rw [Fin.sum_univ_four]
      change (3 : ℤ)^2 + 3^2 + 11^2 + 12^2 = 283
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_03_00_08_01
#print axioms Paper7MomentGapNumeric.valid_03_00_08_01

def qvalues_03_00_08_01 : Fin 19 → ℕ := ![0, 4, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.qvalues_03_00_08_01

theorem row_03_00_08_01 : b4RowContribution (![3, 3, 11, 12] : Fin 4 → ℕ) = 84 := by
  calc
    b4RowContribution (![3, 3, 11, 12] : Fin 4 → ℕ) =
        sparseRowValue ({1, 7} : Finset (Fin 19)) (fun _ => layers_03_00_08_01) :=
      sparseRow_sound (![3, 3, 11, 12] : Fin 4 → ℕ) ({1, 7} : Finset (Fin 19)) (fun _ => layers_03_00_08_01) valid_03_00_08_01
    _ = 84 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_03_00_08_01 Q := by
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
        _ = 84 := by decide
#print axioms Paper7MomentGapNumeric.row_03_00_08_01

theorem weighted_03_00_08_01 : b4RawGapContribution ![3, 0, 8, 1] = 1008 := by
  calc
    b4RawGapContribution ![3, 0, 8, 1] = b4GapPatternWeight 0 8 1 * 84 :=
      b4GapContribution_from_row 3 0 8 1 84 row_03_00_08_01
    _ = 1008 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_08_01

theorem row_03_00_08_02 : b4RowContribution (![3, 3, 11, 13] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 11, 13] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 11 + 13 = 30
    decide
  have hzsq : (∑ i, (((![3, 3, 11, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 308 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 11^2 + 13^2 = 308
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_08_02

theorem weighted_03_00_08_02 : b4RawGapContribution ![3, 0, 8, 2] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 8, 2] = b4GapPatternWeight 0 8 2 * 0 :=
      b4GapContribution_from_row 3 0 8 2 0 row_03_00_08_02
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_08_02

theorem row_03_00_08_03 : b4RowContribution (![3, 3, 11, 14] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 11, 14] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 11 + 14 = 31
    decide
  have hzsq : (∑ i, (((![3, 3, 11, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 335 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 11^2 + 14^2 = 335
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_08_03

theorem weighted_03_00_08_03 : b4RawGapContribution ![3, 0, 8, 3] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 8, 3] = b4GapPatternWeight 0 8 3 * 0 :=
      b4GapContribution_from_row 3 0 8 3 0 row_03_00_08_03
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_08_03

theorem row_03_00_08_04 : b4RowContribution (![3, 3, 11, 15] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 11, 15] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 11 + 15 = 32
    decide
  have hzsq : (∑ i, (((![3, 3, 11, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 364 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 11^2 + 15^2 = 364
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_08_04

theorem weighted_03_00_08_04 : b4RawGapContribution ![3, 0, 8, 4] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 8, 4] = b4GapPatternWeight 0 8 4 * 0 :=
      b4GapContribution_from_row 3 0 8 4 0 row_03_00_08_04
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_08_04

theorem row_03_00_08_05 : b4RowContribution (![3, 3, 11, 16] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 11, 16] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 11 + 16 = 33
    decide
  have hzsq : (∑ i, (((![3, 3, 11, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 395 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 11^2 + 16^2 = 395
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_08_05

theorem weighted_03_00_08_05 : b4RawGapContribution ![3, 0, 8, 5] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 8, 5] = b4GapPatternWeight 0 8 5 * 0 :=
      b4GapContribution_from_row 3 0 8 5 0 row_03_00_08_05
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_08_05

theorem row_03_00_08_06 : b4RowContribution (![3, 3, 11, 17] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 11, 17] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 11 + 17 = 34
    decide
  have hzsq : (∑ i, (((![3, 3, 11, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 428 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 11^2 + 17^2 = 428
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_08_06

theorem weighted_03_00_08_06 : b4RawGapContribution ![3, 0, 8, 6] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 8, 6] = b4GapPatternWeight 0 8 6 * 0 :=
      b4GapContribution_from_row 3 0 8 6 0 row_03_00_08_06
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_08_06

theorem row_03_00_08_07 : b4RowContribution (![3, 3, 11, 18] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 11, 18] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 11 + 18 = 35
    decide
  have hzsq : (∑ i, (((![3, 3, 11, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 463 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 11^2 + 18^2 = 463
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_08_07

theorem weighted_03_00_08_07 : b4RawGapContribution ![3, 0, 8, 7] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 8, 7] = b4GapPatternWeight 0 8 7 * 0 :=
      b4GapContribution_from_row 3 0 8 7 0 row_03_00_08_07
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_08_07

theorem row_03_00_08_08 : b4RowContribution (![3, 3, 11, 19] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 11, 19] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 11 + 19 = 36
    decide
  have hzsq : (∑ i, (((![3, 3, 11, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 500 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 11^2 + 19^2 = 500
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_08_08

theorem weighted_03_00_08_08 : b4RawGapContribution ![3, 0, 8, 8] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 8, 8] = b4GapPatternWeight 0 8 8 * 0 :=
      b4GapContribution_from_row 3 0 8 8 0 row_03_00_08_08
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_08_08

theorem row_03_00_08_09 : b4RowContribution (![3, 3, 11, 20] : Fin 4 → ℕ) = 0 := by
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![3, 3, 11, 20] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 3 + 3 + 11 + 20 = 37
    decide
  have hzsq : (∑ i, (((![3, 3, 11, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 539 := by
    rw [Fin.sum_univ_four]
    change (3 : ℤ)^2 + 3^2 + 11^2 + 20^2 = 539
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentGapNumeric.row_03_00_08_09

theorem weighted_03_00_08_09 : b4RawGapContribution ![3, 0, 8, 9] = 0 := by
  calc
    b4RawGapContribution ![3, 0, 8, 9] = b4GapPatternWeight 0 8 9 * 0 :=
      b4GapContribution_from_row 3 0 8 9 0 row_03_00_08_09
    _ = 0 := by decide
#print axioms Paper7MomentGapNumeric.weighted_03_00_08_09

def dvalues_03_00_08 : Fin 10 → ℕ := ![0, 1008, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentGapNumeric.dvalues_03_00_08

theorem dblock_03_00_08 : b4GapPatternDBlock 3 0 8 = 1008 := by
  calc
    b4GapPatternDBlock 3 0 8 = ∑ d : Fin 10, dvalues_03_00_08 d := by
      apply b4GapDBlock_of_rows 3 0 8 dvalues_03_00_08
      intro d
      fin_cases d
      · exact weighted_03_00_08_00
      · exact weighted_03_00_08_01
      · exact weighted_03_00_08_02
      · exact weighted_03_00_08_03
      · exact weighted_03_00_08_04
      · exact weighted_03_00_08_05
      · exact weighted_03_00_08_06
      · exact weighted_03_00_08_07
      · exact weighted_03_00_08_08
      · exact weighted_03_00_08_09
    _ = 1008 := by decide
#print axioms Paper7MomentGapNumeric.dblock_03_00_08

end Paper7MomentGapNumeric
