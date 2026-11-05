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

theorem row_08_00 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨0, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨0, by decide⟩⟩) = (![0, 0, 8, 0] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 0] : Fin 4 → ℕ) i) = 8 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 0 = 8
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 0] : Fin 4 → ℕ) i : ℤ)^2)) = 64 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 0^2 = 64
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_00

theorem row_08_01 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨1, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨1, by decide⟩⟩) = (![0, 0, 8, 1] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 1] : Fin 4 → ℕ) i) = 9 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 1 = 9
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 1] : Fin 4 → ℕ) i : ℤ)^2)) = 65 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 1^2 = 65
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_01

theorem row_08_02 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨2, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨2, by decide⟩⟩) = (![0, 0, 8, 2] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 2] : Fin 4 → ℕ) i) = 10 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 2 = 10
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 68 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 2^2 = 68
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_02

theorem row_08_03 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨3, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨3, by decide⟩⟩) = (![0, 0, 8, 3] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 3] : Fin 4 → ℕ) i) = 11 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 3 = 11
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 73 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 3^2 = 73
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_03

theorem row_08_04 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨4, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨4, by decide⟩⟩) = (![0, 0, 8, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 4] : Fin 4 → ℕ) i) = 12 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 4 = 12
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 80 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 4^2 = 80
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_04

theorem row_08_05 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨5, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨5, by decide⟩⟩) = (![0, 0, 8, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 5] : Fin 4 → ℕ) i) = 13 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 5 = 13
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 89 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 5^2 = 89
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_05

theorem row_08_06 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨6, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨6, by decide⟩⟩) = (![0, 0, 8, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 6] : Fin 4 → ℕ) i) = 14 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 6 = 14
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 100 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 6^2 = 100
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_06

theorem row_08_07 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨7, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨7, by decide⟩⟩) = (![0, 0, 8, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 7] : Fin 4 → ℕ) i) = 15 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 7 = 15
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 113 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 7^2 = 113
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_07

theorem row_08_08 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨8, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨8, by decide⟩⟩) = (![0, 0, 8, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 8] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 8 = 16
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 128 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 8^2 = 128
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_08

theorem row_08_09 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩⟩) = (![0, 0, 8, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 9] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 9 = 17
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 145 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 9^2 = 145
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_09

def layers_08_10 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 9, 9, 8, 7, 6, 5, 4, 3, 2, 1]]
#print axioms Paper7MomentBlock00.layers_08_10

theorem cells_08_10 : QTableValid (![0, 0, 8, 10] : Fin 4 → ℕ) layers_08_10 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_08_10

theorem valid_08_10 :
    SparseRowValid (![0, 0, 8, 10] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_08_10) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 8, 10] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 8 + 10 = 18
      decide
    have hzsq : (∑ i, (((![0, 0, 8, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 164 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 8^2 + 10^2 = 164
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_08_10
#print axioms Paper7MomentBlock00.valid_08_10

def qvalues_08_10 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]
#print axioms Paper7MomentBlock00.qvalues_08_10

theorem row_08_10 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩⟩) = (![0, 0, 8, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 8, 10] : Fin 4 → ℕ) =
        sparseRowValue ({17} : Finset (Fin 19)) (fun _ => layers_08_10) :=
      sparseRow_sound (![0, 0, 8, 10] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_08_10) valid_08_10
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_08_10 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 2 := by decide
#print axioms Paper7MomentBlock00.row_08_10

def layers_08_11 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 9, 9, 9, 8, 7, 6, 5, 4, 3, 2]]
#print axioms Paper7MomentBlock00.layers_08_11

theorem cells_08_11 : QTableValid (![0, 0, 8, 11] : Fin 4 → ℕ) layers_08_11 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_08_11

theorem valid_08_11 :
    SparseRowValid (![0, 0, 8, 11] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_08_11) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 8, 11] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 8 + 11 = 19
      decide
    have hzsq : (∑ i, (((![0, 0, 8, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 185 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 8^2 + 11^2 = 185
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_08_11
#print axioms Paper7MomentBlock00.valid_08_11

def qvalues_08_11 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_08_11

theorem row_08_11 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩⟩) = 6 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩⟩) = (![0, 0, 8, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 8, 11] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_08_11) :=
      sparseRow_sound (![0, 0, 8, 11] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_08_11) valid_08_11
    _ = 6 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_08_11 Q := by
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
        _ = 6 := by decide
#print axioms Paper7MomentBlock00.row_08_11

def layers_08_12 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 9, 9, 9, 9, 8, 7, 6, 5, 4, 3]]
#print axioms Paper7MomentBlock00.layers_08_12

theorem cells_08_12 : QTableValid (![0, 0, 8, 12] : Fin 4 → ℕ) layers_08_12 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_08_12

theorem valid_08_12 :
    SparseRowValid (![0, 0, 8, 12] : Fin 4 → ℕ) ({16} : Finset (Fin 19)) (fun _ => layers_08_12) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 8, 12] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 8 + 12 = 20
      decide
    have hzsq : (∑ i, (((![0, 0, 8, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 208 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 8^2 + 12^2 = 208
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_08_12
#print axioms Paper7MomentBlock00.valid_08_12

def qvalues_08_12 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_08_12

theorem row_08_12 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨12, by decide⟩⟩) = 5 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨12, by decide⟩⟩) = (![0, 0, 8, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 8, 12] : Fin 4 → ℕ) =
        sparseRowValue ({16} : Finset (Fin 19)) (fun _ => layers_08_12) :=
      sparseRow_sound (![0, 0, 8, 12] : Fin 4 → ℕ) ({16} : Finset (Fin 19)) (fun _ => layers_08_12) valid_08_12
    _ = 5 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_08_12 Q := by
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 5 := by decide
#print axioms Paper7MomentBlock00.row_08_12

def layers_08_13 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 9, 9, 9, 9, 9, 8, 7, 6, 5, 4]]
#print axioms Paper7MomentBlock00.layers_08_13

theorem cells_08_13 : QTableValid (![0, 0, 8, 13] : Fin 4 → ℕ) layers_08_13 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_08_13

theorem valid_08_13 :
    SparseRowValid (![0, 0, 8, 13] : Fin 4 → ℕ) ({2, 8, 14} : Finset (Fin 19)) (fun _ => layers_08_13) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 8, 13] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 8 + 13 = 21
      decide
    have hzsq : (∑ i, (((![0, 0, 8, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 233 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 8^2 + 13^2 = 233
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_08_13
#print axioms Paper7MomentBlock00.valid_08_13

def qvalues_08_13 : Fin 19 → ℕ := ![0, 0, 3, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_08_13

theorem row_08_13 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩⟩) = 20 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩⟩) = (![0, 0, 8, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 8, 13] : Fin 4 → ℕ) =
        sparseRowValue ({2, 8, 14} : Finset (Fin 19)) (fun _ => layers_08_13) :=
      sparseRow_sound (![0, 0, 8, 13] : Fin 4 → ℕ) ({2, 8, 14} : Finset (Fin 19)) (fun _ => layers_08_13) valid_08_13
    _ = 20 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_08_13 Q := by
          apply Finset.sum_congr rfl
          intro Q _
          fin_cases Q
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
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 20 := by decide
#print axioms Paper7MomentBlock00.row_08_13

theorem row_08_14 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨14, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨14, by decide⟩⟩) = (![0, 0, 8, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 14] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 14 = 22
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 260 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 14^2 = 260
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_14

def layers_08_15 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 9, 9, 9, 9, 9, 9, 9, 8, 7, 6]]
#print axioms Paper7MomentBlock00.layers_08_15

theorem cells_08_15 : QTableValid (![0, 0, 8, 15] : Fin 4 → ℕ) layers_08_15 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_08_15

theorem valid_08_15 :
    SparseRowValid (![0, 0, 8, 15] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_08_15) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 8, 15] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 8 + 15 = 23
      decide
    have hzsq : (∑ i, (((![0, 0, 8, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 289 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 8^2 + 15^2 = 289
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_08_15
#print axioms Paper7MomentBlock00.valid_08_15

def qvalues_08_15 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_08_15

theorem row_08_15 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨15, by decide⟩⟩) = 17 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨15, by decide⟩⟩) = (![0, 0, 8, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 8, 15] : Fin 4 → ℕ) =
        sparseRowValue ({7, 13} : Finset (Fin 19)) (fun _ => layers_08_15) :=
      sparseRow_sound (![0, 0, 8, 15] : Fin 4 → ℕ) ({7, 13} : Finset (Fin 19)) (fun _ => layers_08_15) valid_08_15
    _ = 17 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_08_15 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 17 := by decide
#print axioms Paper7MomentBlock00.row_08_15

theorem row_08_16 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨16, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨16, by decide⟩⟩) = (![0, 0, 8, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 16] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 16 = 24
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 320 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 16^2 = 320
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_16

theorem row_08_17 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨17, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨17, by decide⟩⟩) = (![0, 0, 8, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 17] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 17 = 25
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 353 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 17^2 = 353
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_17

theorem row_08_18 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨18, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨18, by decide⟩⟩) = (![0, 0, 8, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 18] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 18 = 26
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 388 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 18^2 = 388
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_18

theorem row_08_19 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨19, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨19, by decide⟩⟩) = (![0, 0, 8, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 19] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 19 = 27
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 425 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 19^2 = 425
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_19

theorem row_08_20 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨20, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨20, by decide⟩⟩) = (![0, 0, 8, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 20] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 20 = 28
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 464 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 20^2 = 464
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_20

theorem row_08_21 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨21, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨21, by decide⟩⟩) = (![0, 0, 8, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 21] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 21 = 29
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 505 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 21^2 = 505
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_21

theorem row_08_22 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨22, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨22, by decide⟩⟩) = (![0, 0, 8, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 22] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 22 = 30
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 548 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 22^2 = 548
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_22

theorem row_08_23 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨23, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨23, by decide⟩⟩) = (![0, 0, 8, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 23] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 23 = 31
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 593 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 23^2 = 593
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_23

theorem row_08_24 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨24, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨24, by decide⟩⟩) = (![0, 0, 8, 24] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 24] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 24 = 32
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 24] : Fin 4 → ℕ) i : ℤ)^2)) = 640 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 24^2 = 640
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_24

theorem row_08_25 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨25, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨25, by decide⟩⟩) = (![0, 0, 8, 25] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 25] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 25 = 33
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 25] : Fin 4 → ℕ) i : ℤ)^2)) = 689 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 25^2 = 689
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_25

theorem row_08_26 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨26, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨26, by decide⟩⟩) = (![0, 0, 8, 26] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 26] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 26 = 34
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 26] : Fin 4 → ℕ) i : ℤ)^2)) = 740 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 26^2 = 740
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_26

theorem row_08_27 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨27, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨27, by decide⟩⟩) = (![0, 0, 8, 27] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 27] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 27 = 35
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 27] : Fin 4 → ℕ) i : ℤ)^2)) = 793 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 27^2 = 793
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_27

theorem row_08_28 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨28, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨28, by decide⟩⟩) = (![0, 0, 8, 28] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 28] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 28 = 36
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 28] : Fin 4 → ℕ) i : ℤ)^2)) = 848 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 28^2 = 848
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_28

theorem row_08_29 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨29, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, ⟨29, by decide⟩⟩) = (![0, 0, 8, 29] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 8, 29] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 8 + 29 = 37
    decide
  have hzsq : (∑ i, (((![0, 0, 8, 29] : Fin 4 → ℕ) i : ℤ)^2)) = 905 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 8^2 + 29^2 = 905
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_08_29

def values_08 : Fin 30 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 5, 20, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.values_08

theorem column_08 :
    (∑ d : Fin 30, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, d⟩)) = 50 := by
  calc
    (∑ d : Fin 30, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨8, by decide⟩, d⟩)) =
        ∑ d : Fin 30, values_08 d := by
      apply Finset.sum_congr rfl
      intro d _
      fin_cases d
      · exact row_08_00
      · exact row_08_01
      · exact row_08_02
      · exact row_08_03
      · exact row_08_04
      · exact row_08_05
      · exact row_08_06
      · exact row_08_07
      · exact row_08_08
      · exact row_08_09
      · exact row_08_10
      · exact row_08_11
      · exact row_08_12
      · exact row_08_13
      · exact row_08_14
      · exact row_08_15
      · exact row_08_16
      · exact row_08_17
      · exact row_08_18
      · exact row_08_19
      · exact row_08_20
      · exact row_08_21
      · exact row_08_22
      · exact row_08_23
      · exact row_08_24
      · exact row_08_25
      · exact row_08_26
      · exact row_08_27
      · exact row_08_28
      · exact row_08_29
    _ = 50 := by decide
#print axioms Paper7MomentBlock00.column_08

end Paper7MomentBlock00
