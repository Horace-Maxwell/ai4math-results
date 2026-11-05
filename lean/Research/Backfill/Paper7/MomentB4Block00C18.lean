import Research.Backfill.Paper7.SparseRowCertificate
import Research.Backfill.Paper7.MomentB4PrefixBlocks

/-! Generated UNTRUSTED proof-source candidate for the complete B4 prefix (0,0).
No native candidate flag, declared count, or data-file coverage is a hypothesis.
Each finite row/DP-cell proof must be accepted by the Lean kernel. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentBlock00
open Paper7MomentCertificate Paper7MomentCounts Paper7MomentDP
open scoped BigOperators

theorem row_18_00 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨0, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨0, by decide⟩⟩) = (![0, 0, 18, 0] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 0] : Fin 4 → ℕ) i) = 18 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 0 = 18
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 0] : Fin 4 → ℕ) i : ℤ)^2)) = 324 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 0^2 = 324
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_00

theorem row_18_01 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨1, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨1, by decide⟩⟩) = (![0, 0, 18, 1] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 1] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 1 = 19
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 1] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 1^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_01

theorem row_18_02 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨2, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨2, by decide⟩⟩) = (![0, 0, 18, 2] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 2] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 2 = 20
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 328 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 2^2 = 328
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_02

theorem row_18_03 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨3, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨3, by decide⟩⟩) = (![0, 0, 18, 3] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 3] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 3 = 21
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 333 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 3^2 = 333
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_03

theorem row_18_04 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨4, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨4, by decide⟩⟩) = (![0, 0, 18, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 4] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 4 = 22
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 340 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 4^2 = 340
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_04

theorem row_18_05 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨5, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨5, by decide⟩⟩) = (![0, 0, 18, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 5] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 5 = 23
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 349 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 5^2 = 349
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_05

theorem row_18_06 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨6, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨6, by decide⟩⟩) = (![0, 0, 18, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 6] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 6 = 24
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 360 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 6^2 = 360
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_06

theorem row_18_07 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨7, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨7, by decide⟩⟩) = (![0, 0, 18, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 7] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 7 = 25
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 373 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 7^2 = 373
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_07

theorem row_18_08 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨8, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨8, by decide⟩⟩) = (![0, 0, 18, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 8] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 8 = 26
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 388 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 8^2 = 388
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_08

theorem row_18_09 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨9, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨9, by decide⟩⟩) = (![0, 0, 18, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 9] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 9 = 27
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 405 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 9^2 = 405
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_09

theorem row_18_10 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨10, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨10, by decide⟩⟩) = (![0, 0, 18, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 10] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 10 = 28
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 424 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 10^2 = 424
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_10

theorem row_18_11 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨11, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨11, by decide⟩⟩) = (![0, 0, 18, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 11] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 11 = 29
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 445 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 11^2 = 445
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_11

theorem row_18_12 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨12, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨12, by decide⟩⟩) = (![0, 0, 18, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 12] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 12 = 30
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 468 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 12^2 = 468
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_12

theorem row_18_13 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨13, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨13, by decide⟩⟩) = (![0, 0, 18, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 13] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 13 = 31
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 493 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 13^2 = 493
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_13

theorem row_18_14 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨14, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨14, by decide⟩⟩) = (![0, 0, 18, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 14] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 14 = 32
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 520 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 14^2 = 520
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_14

theorem row_18_15 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨15, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨15, by decide⟩⟩) = (![0, 0, 18, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 15] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 15 = 33
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 549 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 15^2 = 549
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_15

theorem row_18_16 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨16, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨16, by decide⟩⟩) = (![0, 0, 18, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 16] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 16 = 34
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 580 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 16^2 = 580
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_16

theorem row_18_17 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨17, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨17, by decide⟩⟩) = (![0, 0, 18, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 17] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 17 = 35
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 613 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 17^2 = 613
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_17

theorem row_18_18 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨18, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨18, by decide⟩⟩) = (![0, 0, 18, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 18] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 18 = 36
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 648 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 18^2 = 648
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_18

theorem row_18_19 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩⟩) = (![0, 0, 18, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 18, 19] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 18 + 19 = 37
    decide
  have hzsq : (∑ i, (((![0, 0, 18, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 685 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 18^2 + 19^2 = 685
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_18_19

def values_18 : Fin 20 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.values_18

theorem column_18 :
    (∑ d : Fin 20, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, d⟩)) = 0 := by
  calc
    (∑ d : Fin 20, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨18, by decide⟩, d⟩)) =
        ∑ d : Fin 20, values_18 d := by
      apply Finset.sum_congr rfl
      intro d _
      fin_cases d
      · exact row_18_00
      · exact row_18_01
      · exact row_18_02
      · exact row_18_03
      · exact row_18_04
      · exact row_18_05
      · exact row_18_06
      · exact row_18_07
      · exact row_18_08
      · exact row_18_09
      · exact row_18_10
      · exact row_18_11
      · exact row_18_12
      · exact row_18_13
      · exact row_18_14
      · exact row_18_15
      · exact row_18_16
      · exact row_18_17
      · exact row_18_18
      · exact row_18_19
    _ = 0 := by decide
#print axioms Paper7MomentBlock00.column_18

end Paper7MomentBlock00
