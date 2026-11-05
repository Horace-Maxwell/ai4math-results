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

theorem row_01_00 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩⟩) = (![0, 0, 1, 0] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 0] : Fin 4 → ℕ) i) = 1 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 0 = 1
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 0] : Fin 4 → ℕ) i : ℤ)^2)) = 1 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 0^2 = 1
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_00

theorem row_01_01 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩⟩) = (![0, 0, 1, 1] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 1] : Fin 4 → ℕ) i) = 2 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 1 = 2
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 1] : Fin 4 → ℕ) i : ℤ)^2)) = 2 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 1^2 = 2
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_01

theorem row_01_02 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩⟩) = (![0, 0, 1, 2] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 2] : Fin 4 → ℕ) i) = 3 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 2 = 3
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 5 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 2^2 = 5
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_02

theorem row_01_03 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩⟩) = (![0, 0, 1, 3] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 3] : Fin 4 → ℕ) i) = 4 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 3 = 4
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 10 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 3^2 = 10
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_03

theorem row_01_04 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨4, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨4, by decide⟩⟩) = (![0, 0, 1, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 4] : Fin 4 → ℕ) i) = 5 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 4 = 5
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 17 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 4^2 = 17
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_04

theorem row_01_05 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨5, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨5, by decide⟩⟩) = (![0, 0, 1, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 5] : Fin 4 → ℕ) i) = 6 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 5 = 6
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 26 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 5^2 = 26
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_05

def layers_01_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_01_06

theorem cells_01_06 : QTableValid (![0, 0, 1, 6] : Fin 4 → ℕ) layers_01_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_01_06

theorem valid_01_06 :
    SparseRowValid (![0, 0, 1, 6] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 1, 6] : Fin 4 → ℕ) i) = 7 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 1 + 6 = 7
      decide
    have hzsq : (∑ i, (((![0, 0, 1, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 37 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 1^2 + 6^2 = 37
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_06
#print axioms Paper7MomentBlock00.valid_01_06

def qvalues_01_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_01_06

theorem row_01_06 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨6, by decide⟩⟩) = 1 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨6, by decide⟩⟩) = (![0, 0, 1, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 1, 6] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_01_06) :=
      sparseRow_sound (![0, 0, 1, 6] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_01_06) valid_01_06
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_06 Q := by
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
        _ = 1 := by decide
#print axioms Paper7MomentBlock00.row_01_06

def layers_01_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_01_07

theorem cells_01_07 : QTableValid (![0, 0, 1, 7] : Fin 4 → ℕ) layers_01_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_01_07

theorem valid_01_07 :
    SparseRowValid (![0, 0, 1, 7] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_01_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 1, 7] : Fin 4 → ℕ) i) = 8 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 1 + 7 = 8
      decide
    have hzsq : (∑ i, (((![0, 0, 1, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 50 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 1^2 + 7^2 = 50
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_07
#print axioms Paper7MomentBlock00.valid_01_07

def qvalues_01_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_01_07

theorem row_01_07 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨7, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨7, by decide⟩⟩) = (![0, 0, 1, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 1, 7] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_01_07) :=
      sparseRow_sound (![0, 0, 1, 7] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_01_07) valid_01_07
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_07 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 2 := by decide
#print axioms Paper7MomentBlock00.row_01_07

theorem row_01_08 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨8, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨8, by decide⟩⟩) = (![0, 0, 1, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 8] : Fin 4 → ℕ) i) = 9 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 8 = 9
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 65 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 8^2 = 65
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_08

theorem row_01_09 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨9, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨9, by decide⟩⟩) = (![0, 0, 1, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 9] : Fin 4 → ℕ) i) = 10 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 9 = 10
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 82 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 9^2 = 82
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_09

theorem row_01_10 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨10, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨10, by decide⟩⟩) = (![0, 0, 1, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 10] : Fin 4 → ℕ) i) = 11 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 10 = 11
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 101 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 10^2 = 101
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_10

theorem row_01_11 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨11, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨11, by decide⟩⟩) = (![0, 0, 1, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 11] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 11 = 12
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 122 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 11^2 = 122
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_11

theorem row_01_12 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨12, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨12, by decide⟩⟩) = (![0, 0, 1, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 12] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 12 = 13
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 145 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 12^2 = 145
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_12

def layers_01_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_01_13

theorem cells_01_13 : QTableValid (![0, 0, 1, 13] : Fin 4 → ℕ) layers_01_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_01_13

theorem valid_01_13 :
    SparseRowValid (![0, 0, 1, 13] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_01_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 1, 13] : Fin 4 → ℕ) i) = 14 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 1 + 13 = 14
      decide
    have hzsq : (∑ i, (((![0, 0, 1, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 170 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 1^2 + 13^2 = 170
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_13
#print axioms Paper7MomentBlock00.valid_01_13

def qvalues_01_13 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_01_13

theorem row_01_13 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨13, by decide⟩⟩) = 1 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨13, by decide⟩⟩) = (![0, 0, 1, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 1, 13] : Fin 4 → ℕ) =
        sparseRowValue ({14} : Finset (Fin 19)) (fun _ => layers_01_13) :=
      sparseRow_sound (![0, 0, 1, 13] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_01_13) valid_01_13
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_13 Q := by
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
        _ = 1 := by decide
#print axioms Paper7MomentBlock00.row_01_13

def layers_01_14 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_01_14

theorem cells_01_14 : QTableValid (![0, 0, 1, 14] : Fin 4 → ℕ) layers_01_14 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_01_14

theorem valid_01_14 :
    SparseRowValid (![0, 0, 1, 14] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_01_14) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 1, 14] : Fin 4 → ℕ) i) = 15 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 1 + 14 = 15
      decide
    have hzsq : (∑ i, (((![0, 0, 1, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 197 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 1^2 + 14^2 = 197
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_14
#print axioms Paper7MomentBlock00.valid_01_14

def qvalues_01_14 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_01_14

theorem row_01_14 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨14, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨14, by decide⟩⟩) = (![0, 0, 1, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 1, 14] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_01_14) :=
      sparseRow_sound (![0, 0, 1, 14] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_01_14) valid_01_14
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_14 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 2 := by decide
#print axioms Paper7MomentBlock00.row_01_14

def layers_01_15 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0]]
#print axioms Paper7MomentBlock00.layers_01_15

theorem cells_01_15 : QTableValid (![0, 0, 1, 15] : Fin 4 → ℕ) layers_01_15 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_01_15

theorem valid_01_15 :
    SparseRowValid (![0, 0, 1, 15] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_01_15) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 1, 15] : Fin 4 → ℕ) i) = 16 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 1 + 15 = 16
      decide
    have hzsq : (∑ i, (((![0, 0, 1, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 226 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 1^2 + 15^2 = 226
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_15
#print axioms Paper7MomentBlock00.valid_01_15

def qvalues_01_15 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_01_15

theorem row_01_15 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨15, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨15, by decide⟩⟩) = (![0, 0, 1, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 1, 15] : Fin 4 → ℕ) =
        sparseRowValue ({13} : Finset (Fin 19)) (fun _ => layers_01_15) :=
      sparseRow_sound (![0, 0, 1, 15] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_01_15) valid_01_15
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_15 Q := by
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
        _ = 2 := by decide
#print axioms Paper7MomentBlock00.row_01_15

theorem row_01_16 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨16, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨16, by decide⟩⟩) = (![0, 0, 1, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 16] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 16 = 17
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 257 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 16^2 = 257
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_16

def layers_01_17 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1]]
#print axioms Paper7MomentBlock00.layers_01_17

theorem cells_01_17 : QTableValid (![0, 0, 1, 17] : Fin 4 → ℕ) layers_01_17 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_01_17

theorem valid_01_17 :
    SparseRowValid (![0, 0, 1, 17] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_01_17) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 1, 17] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 1 + 17 = 18
      decide
    have hzsq : (∑ i, (((![0, 0, 1, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 290 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 1^2 + 17^2 = 290
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_17
#print axioms Paper7MomentBlock00.valid_01_17

def qvalues_01_17 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_01_17

theorem row_01_17 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨17, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨17, by decide⟩⟩) = (![0, 0, 1, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 1, 17] : Fin 4 → ℕ) =
        sparseRowValue ({14} : Finset (Fin 19)) (fun _ => layers_01_17) :=
      sparseRow_sound (![0, 0, 1, 17] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_01_17) valid_01_17
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_17 Q := by
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
        _ = 2 := by decide
#print axioms Paper7MomentBlock00.row_01_17

theorem row_01_18 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨18, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨18, by decide⟩⟩) = (![0, 0, 1, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 18] : Fin 4 → ℕ) i) = 19 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 18 = 19
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 325 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 18^2 = 325
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_18

theorem row_01_19 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨19, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨19, by decide⟩⟩) = (![0, 0, 1, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 19] : Fin 4 → ℕ) i) = 20 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 19 = 20
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 362 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 19^2 = 362
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_19

theorem row_01_20 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨20, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨20, by decide⟩⟩) = (![0, 0, 1, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 20] : Fin 4 → ℕ) i) = 21 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 20 = 21
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 401 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 20^2 = 401
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_20

theorem row_01_21 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨21, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨21, by decide⟩⟩) = (![0, 0, 1, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 21] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 21 = 22
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 442 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 21^2 = 442
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_21

theorem row_01_22 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨22, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨22, by decide⟩⟩) = (![0, 0, 1, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 22] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 22 = 23
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 485 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 22^2 = 485
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_22

def layers_01_23 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]]
#print axioms Paper7MomentBlock00.layers_01_23

theorem cells_01_23 : QTableValid (![0, 0, 1, 23] : Fin 4 → ℕ) layers_01_23 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_01_23

theorem valid_01_23 :
    SparseRowValid (![0, 0, 1, 23] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_01_23) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 1, 23] : Fin 4 → ℕ) i) = 24 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 1 + 23 = 24
      decide
    have hzsq : (∑ i, (((![0, 0, 1, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 530 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 1^2 + 23^2 = 530
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_23
#print axioms Paper7MomentBlock00.valid_01_23

def qvalues_01_23 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_01_23

theorem row_01_23 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨23, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨23, by decide⟩⟩) = (![0, 0, 1, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 1, 23] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_01_23) :=
      sparseRow_sound (![0, 0, 1, 23] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_01_23) valid_01_23
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_23 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 2 := by decide
#print axioms Paper7MomentBlock00.row_01_23

def layers_01_24 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]]
#print axioms Paper7MomentBlock00.layers_01_24

theorem cells_01_24 : QTableValid (![0, 0, 1, 24] : Fin 4 → ℕ) layers_01_24 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_01_24

theorem valid_01_24 :
    SparseRowValid (![0, 0, 1, 24] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_24) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 1, 24] : Fin 4 → ℕ) i) = 25 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 1 + 24 = 25
      decide
    have hzsq : (∑ i, (((![0, 0, 1, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 577 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 1^2 + 24^2 = 577
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_01_24
#print axioms Paper7MomentBlock00.valid_01_24

def qvalues_01_24 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_01_24

theorem row_01_24 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨24, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨24, by decide⟩⟩) = (![0, 0, 1, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 1, 24] : Fin 4 → ℕ) =
        sparseRowValue ({10} : Finset (Fin 19)) (fun _ => layers_01_24) :=
      sparseRow_sound (![0, 0, 1, 24] : Fin 4 → ℕ) ({10} : Finset (Fin 19)) (fun _ => layers_01_24) valid_01_24
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_01_24 Q := by
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
        _ = 2 := by decide
#print axioms Paper7MomentBlock00.row_01_24

theorem row_01_25 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨25, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨25, by decide⟩⟩) = (![0, 0, 1, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 25] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 25 = 26
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 626 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 25^2 = 626
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_25

theorem row_01_26 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨26, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨26, by decide⟩⟩) = (![0, 0, 1, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 26] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 26 = 27
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 677 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 26^2 = 677
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_26

theorem row_01_27 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨27, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨27, by decide⟩⟩) = (![0, 0, 1, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 27] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 27 = 28
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 730 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 27^2 = 730
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_27

theorem row_01_28 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨28, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨28, by decide⟩⟩) = (![0, 0, 1, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 28] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 28 = 29
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 785 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 28^2 = 785
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_28

theorem row_01_29 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨29, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨29, by decide⟩⟩) = (![0, 0, 1, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 29] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 29 = 30
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 842 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 29^2 = 842
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_29

theorem row_01_30 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨30, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨30, by decide⟩⟩) = (![0, 0, 1, 30] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 30] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 30 = 31
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 901 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 30^2 = 901
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_30

theorem row_01_31 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨31, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨31, by decide⟩⟩) = (![0, 0, 1, 31] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 31] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 31 = 32
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 31] : Fin 4 → ℕ) i : ℤ)^2)) = 962 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 31^2 = 962
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_31

theorem row_01_32 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨32, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨32, by decide⟩⟩) = (![0, 0, 1, 32] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 32] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 32 = 33
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 32] : Fin 4 → ℕ) i : ℤ)^2)) = 1025 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 32^2 = 1025
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_32

theorem row_01_33 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨33, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨33, by decide⟩⟩) = (![0, 0, 1, 33] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 33] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 33 = 34
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 33] : Fin 4 → ℕ) i : ℤ)^2)) = 1090 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 33^2 = 1090
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_33

theorem row_01_34 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨34, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨34, by decide⟩⟩) = (![0, 0, 1, 34] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 34] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 34 = 35
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 34] : Fin 4 → ℕ) i : ℤ)^2)) = 1157 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 34^2 = 1157
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_34

theorem row_01_35 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨35, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨35, by decide⟩⟩) = (![0, 0, 1, 35] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 35] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 35 = 36
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 35] : Fin 4 → ℕ) i : ℤ)^2)) = 1226 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 35^2 = 1226
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_35

theorem row_01_36 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨36, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨36, by decide⟩⟩) = (![0, 0, 1, 36] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 1, 36] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 1 + 36 = 37
    decide
  have hzsq : (∑ i, (((![0, 0, 1, 36] : Fin 4 → ℕ) i : ℤ)^2)) = 1297 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 1^2 + 36^2 = 1297
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_01_36

def values_01 : Fin 37 → ℕ := ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 1, 2, 2, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.values_01

theorem column_01 :
    (∑ d : Fin 37, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, d⟩)) = 14 := by
  calc
    (∑ d : Fin 37, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, d⟩)) =
        ∑ d : Fin 37, values_01 d := by
      apply Finset.sum_congr rfl
      intro d _
      fin_cases d
      · exact row_01_00
      · exact row_01_01
      · exact row_01_02
      · exact row_01_03
      · exact row_01_04
      · exact row_01_05
      · exact row_01_06
      · exact row_01_07
      · exact row_01_08
      · exact row_01_09
      · exact row_01_10
      · exact row_01_11
      · exact row_01_12
      · exact row_01_13
      · exact row_01_14
      · exact row_01_15
      · exact row_01_16
      · exact row_01_17
      · exact row_01_18
      · exact row_01_19
      · exact row_01_20
      · exact row_01_21
      · exact row_01_22
      · exact row_01_23
      · exact row_01_24
      · exact row_01_25
      · exact row_01_26
      · exact row_01_27
      · exact row_01_28
      · exact row_01_29
      · exact row_01_30
      · exact row_01_31
      · exact row_01_32
      · exact row_01_33
      · exact row_01_34
      · exact row_01_35
      · exact row_01_36
    _ = 14 := by decide
#print axioms Paper7MomentBlock00.column_01

end Paper7MomentBlock00
