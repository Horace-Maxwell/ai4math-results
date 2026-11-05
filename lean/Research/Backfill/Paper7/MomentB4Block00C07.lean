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

def layers_07_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_07_00

theorem cells_07_00 : QTableValid (![0, 0, 7, 0] : Fin 4 → ℕ) layers_07_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_07_00

theorem valid_07_00 :
    SparseRowValid (![0, 0, 7, 0] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_07_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 7, 0] : Fin 4 → ℕ) i) = 7 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 7 + 0 = 7
      decide
    have hzsq : (∑ i, (((![0, 0, 7, 0] : Fin 4 → ℕ) i : ℤ)^2)) = 49 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 7^2 + 0^2 = 49
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_07_00
#print axioms Paper7MomentBlock00.valid_07_00

def qvalues_07_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_07_00

theorem row_07_00 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨0, by decide⟩⟩) = 1 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨0, by decide⟩⟩) = (![0, 0, 7, 0] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 7, 0] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_07_00) :=
      sparseRow_sound (![0, 0, 7, 0] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_07_00) valid_07_00
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_07_00 Q := by
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
#print axioms Paper7MomentBlock00.row_07_00

def layers_07_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_07_01

theorem cells_07_01 : QTableValid (![0, 0, 7, 1] : Fin 4 → ℕ) layers_07_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_07_01

theorem valid_07_01 :
    SparseRowValid (![0, 0, 7, 1] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_07_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 7, 1] : Fin 4 → ℕ) i) = 8 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 7 + 1 = 8
      decide
    have hzsq : (∑ i, (((![0, 0, 7, 1] : Fin 4 → ℕ) i : ℤ)^2)) = 50 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 7^2 + 1^2 = 50
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_07_01
#print axioms Paper7MomentBlock00.valid_07_01

def qvalues_07_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_07_01

theorem row_07_01 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨1, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨1, by decide⟩⟩) = (![0, 0, 7, 1] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 7, 1] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_07_01) :=
      sparseRow_sound (![0, 0, 7, 1] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_07_01) valid_07_01
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_07_01 Q := by
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
#print axioms Paper7MomentBlock00.row_07_01

theorem row_07_02 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨2, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨2, by decide⟩⟩) = (![0, 0, 7, 2] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 2] : Fin 4 → ℕ) i) = 9 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 2 = 9
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 53 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 2^2 = 53
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_02

theorem row_07_03 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨3, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨3, by decide⟩⟩) = (![0, 0, 7, 3] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 3] : Fin 4 → ℕ) i) = 10 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 3 = 10
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 58 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 3^2 = 58
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_03

theorem row_07_04 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨4, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨4, by decide⟩⟩) = (![0, 0, 7, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 4] : Fin 4 → ℕ) i) = 11 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 4 = 11
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 65 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 4^2 = 65
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_04

theorem row_07_05 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨5, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨5, by decide⟩⟩) = (![0, 0, 7, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 5] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 5 = 12
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 74 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 5^2 = 74
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_05

theorem row_07_06 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨6, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨6, by decide⟩⟩) = (![0, 0, 7, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 6] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 6 = 13
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 85 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 6^2 = 85
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_06

theorem row_07_07 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨7, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨7, by decide⟩⟩) = (![0, 0, 7, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 7] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 7 = 14
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 98 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 7^2 = 98
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_07

theorem row_07_08 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩⟩) = (![0, 0, 7, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 8] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 8 = 15
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 113 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 8^2 = 113
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_08

theorem row_07_09 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩⟩) = (![0, 0, 7, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 9] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 9 = 16
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 130 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 9^2 = 130
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_09

theorem row_07_10 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨10, by decide⟩⟩) = (![0, 0, 7, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 10] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 10 = 17
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 149 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 10^2 = 149
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_10

def layers_07_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 8, 8, 8, 8, 7, 6, 5, 4, 3, 2, 1]]
#print axioms Paper7MomentBlock00.layers_07_11

theorem cells_07_11 : QTableValid (![0, 0, 7, 11] : Fin 4 → ℕ) layers_07_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_07_11

theorem valid_07_11 :
    SparseRowValid (![0, 0, 7, 11] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_07_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 7, 11] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 7 + 11 = 18
      decide
    have hzsq : (∑ i, (((![0, 0, 7, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 170 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 7^2 + 11^2 = 170
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_07_11
#print axioms Paper7MomentBlock00.valid_07_11

def qvalues_07_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_07_11

theorem row_07_11 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩⟩) = 5 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨11, by decide⟩⟩) = (![0, 0, 7, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 7, 11] : Fin 4 → ℕ) =
        sparseRowValue ({14} : Finset (Fin 19)) (fun _ => layers_07_11) :=
      sparseRow_sound (![0, 0, 7, 11] : Fin 4 → ℕ) ({14} : Finset (Fin 19)) (fun _ => layers_07_11) valid_07_11
    _ = 5 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_07_11 Q := by
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
        _ = 5 := by decide
#print axioms Paper7MomentBlock00.row_07_11

def layers_07_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 8, 8, 8, 8, 8, 7, 6, 5, 4, 3, 2]]
#print axioms Paper7MomentBlock00.layers_07_12

theorem cells_07_12 : QTableValid (![0, 0, 7, 12] : Fin 4 → ℕ) layers_07_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_07_12

theorem valid_07_12 :
    SparseRowValid (![0, 0, 7, 12] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_07_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 7, 12] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 7 + 12 = 19
      decide
    have hzsq : (∑ i, (((![0, 0, 7, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 193 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 7^2 + 12^2 = 193
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_07_12
#print axioms Paper7MomentBlock00.valid_07_12

def qvalues_07_12 : Fin 19 → ℕ := ![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_07_12

theorem row_07_12 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨12, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨12, by decide⟩⟩) = (![0, 0, 7, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 7, 12] : Fin 4 → ℕ) =
        sparseRowValue ({1} : Finset (Fin 19)) (fun _ => layers_07_12) :=
      sparseRow_sound (![0, 0, 7, 12] : Fin 4 → ℕ) ({1} : Finset (Fin 19)) (fun _ => layers_07_12) valid_07_12
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_07_12 Q := by
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
#print axioms Paper7MomentBlock00.row_07_12

def layers_07_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 8, 8, 8, 8, 8, 8, 7, 6, 5, 4, 3]]
#print axioms Paper7MomentBlock00.layers_07_13

theorem cells_07_13 : QTableValid (![0, 0, 7, 13] : Fin 4 → ℕ) layers_07_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_07_13

theorem valid_07_13 :
    SparseRowValid (![0, 0, 7, 13] : Fin 4 → ℕ) ({11, 17} : Finset (Fin 19)) (fun _ => layers_07_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 7, 13] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 7 + 13 = 20
      decide
    have hzsq : (∑ i, (((![0, 0, 7, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 218 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 7^2 + 13^2 = 218
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_07_13
#print axioms Paper7MomentBlock00.valid_07_13

def qvalues_07_13 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 4, 0]
#print axioms Paper7MomentBlock00.qvalues_07_13

theorem row_07_13 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨13, by decide⟩⟩) = 12 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨13, by decide⟩⟩) = (![0, 0, 7, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 7, 13] : Fin 4 → ℕ) =
        sparseRowValue ({11, 17} : Finset (Fin 19)) (fun _ => layers_07_13) :=
      sparseRow_sound (![0, 0, 7, 13] : Fin 4 → ℕ) ({11, 17} : Finset (Fin 19)) (fun _ => layers_07_13) valid_07_13
    _ = 12 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_07_13 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 12 := by decide
#print axioms Paper7MomentBlock00.row_07_13

def layers_07_14 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 8, 8, 8, 8, 8, 8, 8, 7, 6, 5, 4]]
#print axioms Paper7MomentBlock00.layers_07_14

theorem cells_07_14 : QTableValid (![0, 0, 7, 14] : Fin 4 → ℕ) layers_07_14 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_07_14

theorem valid_07_14 :
    SparseRowValid (![0, 0, 7, 14] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_07_14) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 7, 14] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 7 + 14 = 21
      decide
    have hzsq : (∑ i, (((![0, 0, 7, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 245 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 7^2 + 14^2 = 245
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_07_14
#print axioms Paper7MomentBlock00.valid_07_14

def qvalues_07_14 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_07_14

theorem row_07_14 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨14, by decide⟩⟩) = 8 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨14, by decide⟩⟩) = (![0, 0, 7, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 7, 14] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_07_14) :=
      sparseRow_sound (![0, 0, 7, 14] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_07_14) valid_07_14
    _ = 8 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_07_14 Q := by
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
        _ = 8 := by decide
#print axioms Paper7MomentBlock00.row_07_14

theorem row_07_15 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨15, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨15, by decide⟩⟩) = (![0, 0, 7, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 15] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 15 = 22
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 274 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 15^2 = 274
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_15

theorem row_07_16 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨16, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨16, by decide⟩⟩) = (![0, 0, 7, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 16] : Fin 4 → ℕ) i) = 23 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 16 = 23
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 305 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 16^2 = 305
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_16

theorem row_07_17 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨17, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨17, by decide⟩⟩) = (![0, 0, 7, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 17] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 17 = 24
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 338 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 17^2 = 338
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_17

theorem row_07_18 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨18, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨18, by decide⟩⟩) = (![0, 0, 7, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 18] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 18 = 25
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 373 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 18^2 = 373
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_18

theorem row_07_19 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨19, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨19, by decide⟩⟩) = (![0, 0, 7, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 19] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 19 = 26
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 410 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 19^2 = 410
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_19

theorem row_07_20 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨20, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨20, by decide⟩⟩) = (![0, 0, 7, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 20] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 20 = 27
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 449 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 20^2 = 449
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_20

theorem row_07_21 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨21, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨21, by decide⟩⟩) = (![0, 0, 7, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 21] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 21 = 28
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 490 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 21^2 = 490
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_21

theorem row_07_22 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨22, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨22, by decide⟩⟩) = (![0, 0, 7, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 22] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 22 = 29
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 533 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 22^2 = 533
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_22

theorem row_07_23 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨23, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨23, by decide⟩⟩) = (![0, 0, 7, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 23] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 23 = 30
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 578 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 23^2 = 578
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_23

theorem row_07_24 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨24, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨24, by decide⟩⟩) = (![0, 0, 7, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 24] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 24 = 31
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 625 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 24^2 = 625
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_24

theorem row_07_25 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨25, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨25, by decide⟩⟩) = (![0, 0, 7, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 25] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 25 = 32
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 674 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 25^2 = 674
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_25

theorem row_07_26 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨26, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨26, by decide⟩⟩) = (![0, 0, 7, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 26] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 26 = 33
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 725 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 26^2 = 725
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_26

theorem row_07_27 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨27, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨27, by decide⟩⟩) = (![0, 0, 7, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 27] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 27 = 34
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 778 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 27^2 = 778
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_27

theorem row_07_28 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨28, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨28, by decide⟩⟩) = (![0, 0, 7, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 28] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 28 = 35
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 833 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 28^2 = 833
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_28

theorem row_07_29 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨29, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨29, by decide⟩⟩) = (![0, 0, 7, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 29] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 29 = 36
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 890 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 29^2 = 890
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_29

theorem row_07_30 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨30, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨30, by decide⟩⟩) = (![0, 0, 7, 30] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 7, 30] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 7 + 30 = 37
    decide
  have hzsq : (∑ i, (((![0, 0, 7, 30] : Fin 4 → ℕ) i : ℤ)^2)) = 949 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 7^2 + 30^2 = 949
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_07_30

def values_07 : Fin 31 → ℕ := ![1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2, 12, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.values_07

theorem column_07 :
    (∑ d : Fin 31, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, d⟩)) = 30 := by
  calc
    (∑ d : Fin 31, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨7, by decide⟩, d⟩)) =
        ∑ d : Fin 31, values_07 d := by
      apply Finset.sum_congr rfl
      intro d _
      fin_cases d
      · exact row_07_00
      · exact row_07_01
      · exact row_07_02
      · exact row_07_03
      · exact row_07_04
      · exact row_07_05
      · exact row_07_06
      · exact row_07_07
      · exact row_07_08
      · exact row_07_09
      · exact row_07_10
      · exact row_07_11
      · exact row_07_12
      · exact row_07_13
      · exact row_07_14
      · exact row_07_15
      · exact row_07_16
      · exact row_07_17
      · exact row_07_18
      · exact row_07_19
      · exact row_07_20
      · exact row_07_21
      · exact row_07_22
      · exact row_07_23
      · exact row_07_24
      · exact row_07_25
      · exact row_07_26
      · exact row_07_27
      · exact row_07_28
      · exact row_07_29
      · exact row_07_30
    _ = 30 := by decide
#print axioms Paper7MomentBlock00.column_07

end Paper7MomentBlock00
