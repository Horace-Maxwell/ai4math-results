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

def layers_14_00 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_14_00

theorem cells_14_00 : QTableValid (![0, 0, 14, 0] : Fin 4 → ℕ) layers_14_00 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_14_00

theorem valid_14_00 :
    SparseRowValid (![0, 0, 14, 0] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_14_00) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 14, 0] : Fin 4 → ℕ) i) = 14 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 14 + 0 = 14
      decide
    have hzsq : (∑ i, (((![0, 0, 14, 0] : Fin 4 → ℕ) i : ℤ)^2)) = 196 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 14^2 + 0^2 = 196
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_14_00
#print axioms Paper7MomentBlock00.valid_14_00

def qvalues_14_00 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_14_00

theorem row_14_00 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨0, by decide⟩⟩) = 1 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨0, by decide⟩⟩) = (![0, 0, 14, 0] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 14, 0] : Fin 4 → ℕ) =
        sparseRowValue ({7} : Finset (Fin 19)) (fun _ => layers_14_00) :=
      sparseRow_sound (![0, 0, 14, 0] : Fin 4 → ℕ) ({7} : Finset (Fin 19)) (fun _ => layers_14_00) valid_14_00
    _ = 1 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_14_00 Q := by
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
#print axioms Paper7MomentBlock00.row_14_00

def layers_14_01 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 0, 0, 0]]
#print axioms Paper7MomentBlock00.layers_14_01

theorem cells_14_01 : QTableValid (![0, 0, 14, 1] : Fin 4 → ℕ) layers_14_01 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_14_01

theorem valid_14_01 :
    SparseRowValid (![0, 0, 14, 1] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_14_01) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 14, 1] : Fin 4 → ℕ) i) = 15 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 14 + 1 = 15
      decide
    have hzsq : (∑ i, (((![0, 0, 14, 1] : Fin 4 → ℕ) i : ℤ)^2)) = 197 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 14^2 + 1^2 = 197
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_14_01
#print axioms Paper7MomentBlock00.valid_14_01

def qvalues_14_01 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_14_01

theorem row_14_01 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨1, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨1, by decide⟩⟩) = (![0, 0, 14, 1] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 14, 1] : Fin 4 → ℕ) =
        sparseRowValue ({5} : Finset (Fin 19)) (fun _ => layers_14_01) :=
      sparseRow_sound (![0, 0, 14, 1] : Fin 4 → ℕ) ({5} : Finset (Fin 19)) (fun _ => layers_14_01) valid_14_01
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_14_01 Q := by
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
#print axioms Paper7MomentBlock00.row_14_01

theorem row_14_02 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨2, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨2, by decide⟩⟩) = (![0, 0, 14, 2] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 2] : Fin 4 → ℕ) i) = 16 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 2 = 16
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 2] : Fin 4 → ℕ) i : ℤ)^2)) = 200 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 2^2 = 200
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_02

theorem row_14_03 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨3, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨3, by decide⟩⟩) = (![0, 0, 14, 3] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 3] : Fin 4 → ℕ) i) = 17 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 3 = 17
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 3] : Fin 4 → ℕ) i : ℤ)^2)) = 205 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 3^2 = 205
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_03

def layers_14_04 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 4, 3, 2, 1]]
#print axioms Paper7MomentBlock00.layers_14_04

theorem cells_14_04 : QTableValid (![0, 0, 14, 4] : Fin 4 → ℕ) layers_14_04 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_14_04

theorem valid_14_04 :
    SparseRowValid (![0, 0, 14, 4] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_14_04) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 14, 4] : Fin 4 → ℕ) i) = 18 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 14 + 4 = 18
      decide
    have hzsq : (∑ i, (((![0, 0, 14, 4] : Fin 4 → ℕ) i : ℤ)^2)) = 212 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 14^2 + 4^2 = 212
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_14_04
#print axioms Paper7MomentBlock00.valid_14_04

def qvalues_14_04 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]
#print axioms Paper7MomentBlock00.qvalues_14_04

theorem row_14_04 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨4, by decide⟩⟩) = 2 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨4, by decide⟩⟩) = (![0, 0, 14, 4] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 14, 4] : Fin 4 → ℕ) =
        sparseRowValue ({17} : Finset (Fin 19)) (fun _ => layers_14_04) :=
      sparseRow_sound (![0, 0, 14, 4] : Fin 4 → ℕ) ({17} : Finset (Fin 19)) (fun _ => layers_14_04) valid_14_04
    _ = 2 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_14_04 Q := by
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
#print axioms Paper7MomentBlock00.row_14_04

def layers_14_05 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 4, 3, 2]]
#print axioms Paper7MomentBlock00.layers_14_05

theorem cells_14_05 : QTableValid (![0, 0, 14, 5] : Fin 4 → ℕ) layers_14_05 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_14_05

theorem valid_14_05 :
    SparseRowValid (![0, 0, 14, 5] : Fin 4 → ℕ) ({11, 17} : Finset (Fin 19)) (fun _ => layers_14_05) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 14, 5] : Fin 4 → ℕ) i) = 19 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 14 + 5 = 19
      decide
    have hzsq : (∑ i, (((![0, 0, 14, 5] : Fin 4 → ℕ) i : ℤ)^2)) = 221 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 14^2 + 5^2 = 221
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_14_05
#print axioms Paper7MomentBlock00.valid_14_05

def qvalues_14_05 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 3, 0]
#print axioms Paper7MomentBlock00.qvalues_14_05

theorem row_14_05 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨5, by decide⟩⟩) = 9 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨5, by decide⟩⟩) = (![0, 0, 14, 5] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 14, 5] : Fin 4 → ℕ) =
        sparseRowValue ({11, 17} : Finset (Fin 19)) (fun _ => layers_14_05) :=
      sparseRow_sound (![0, 0, 14, 5] : Fin 4 → ℕ) ({11, 17} : Finset (Fin 19)) (fun _ => layers_14_05) valid_14_05
    _ = 9 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_14_05 Q := by
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
        _ = 9 := by decide
#print axioms Paper7MomentBlock00.row_14_05

def layers_14_06 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 6, 5, 4, 3]]
#print axioms Paper7MomentBlock00.layers_14_06

theorem cells_14_06 : QTableValid (![0, 0, 14, 6] : Fin 4 → ℕ) layers_14_06 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_14_06

theorem valid_14_06 :
    SparseRowValid (![0, 0, 14, 6] : Fin 4 → ℕ) ({4, 10, 16} : Finset (Fin 19)) (fun _ => layers_14_06) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 14, 6] : Fin 4 → ℕ) i) = 20 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 14 + 6 = 20
      decide
    have hzsq : (∑ i, (((![0, 0, 14, 6] : Fin 4 → ℕ) i : ℤ)^2)) = 232 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 14^2 + 6^2 = 232
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_14_06
#print axioms Paper7MomentBlock00.valid_14_06

def qvalues_14_06 : Fin 19 → ℕ := ![0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 5, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_14_06

theorem row_14_06 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨6, by decide⟩⟩) = 17 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨6, by decide⟩⟩) = (![0, 0, 14, 6] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 14, 6] : Fin 4 → ℕ) =
        sparseRowValue ({4, 10, 16} : Finset (Fin 19)) (fun _ => layers_14_06) :=
      sparseRow_sound (![0, 0, 14, 6] : Fin 4 → ℕ) ({4, 10, 16} : Finset (Fin 19)) (fun _ => layers_14_06) valid_14_06
    _ = 17 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_14_06 Q := by
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
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_left (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
          · exact (dite_eq_right (by norm_num)).trans (by rfl)
        _ = 17 := by decide
#print axioms Paper7MomentBlock00.row_14_06

def layers_14_07 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 8, 8, 8, 8, 8, 8, 8, 7, 6, 5, 4]]
#print axioms Paper7MomentBlock00.layers_14_07

theorem cells_14_07 : QTableValid (![0, 0, 14, 7] : Fin 4 → ℕ) layers_14_07 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_14_07

theorem valid_14_07 :
    SparseRowValid (![0, 0, 14, 7] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_14_07) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 14, 7] : Fin 4 → ℕ) i) = 21 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 14 + 7 = 21
      decide
    have hzsq : (∑ i, (((![0, 0, 14, 7] : Fin 4 → ℕ) i : ℤ)^2)) = 245 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 14^2 + 7^2 = 245
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_14_07
#print axioms Paper7MomentBlock00.valid_14_07

def qvalues_14_07 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_14_07

theorem row_14_07 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨7, by decide⟩⟩) = 8 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨7, by decide⟩⟩) = (![0, 0, 14, 7] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 14, 7] : Fin 4 → ℕ) =
        sparseRowValue ({8} : Finset (Fin 19)) (fun _ => layers_14_07) :=
      sparseRow_sound (![0, 0, 14, 7] : Fin 4 → ℕ) ({8} : Finset (Fin 19)) (fun _ => layers_14_07) valid_14_07
    _ = 8 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_14_07 Q := by
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
#print axioms Paper7MomentBlock00.row_14_07

theorem row_14_08 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨8, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨8, by decide⟩⟩) = (![0, 0, 14, 8] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 8] : Fin 4 → ℕ) i) = 22 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 8 = 22
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 8] : Fin 4 → ℕ) i : ℤ)^2)) = 260 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 8^2 = 260
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_08

def layers_14_09 : Fin 5 → Fin 19 → ℕ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0], ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 10, 10, 10, 10, 9, 8, 7, 6]]
#print axioms Paper7MomentBlock00.layers_14_09

theorem cells_14_09 : QTableValid (![0, 0, 14, 9] : Fin 4 → ℕ) layers_14_09 := by
  unfold QTableValid
  constructor
  · intro t
    fin_cases t <;> decide
  · intro k t
    fin_cases k <;> fin_cases t <;> decide
#print axioms Paper7MomentBlock00.cells_14_09

theorem valid_14_09 :
    SparseRowValid (![0, 0, 14, 9] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_14_09) := by
  constructor
  · intro Q
    have hzsum : (∑ i, (![0, 0, 14, 9] : Fin 4 → ℕ) i) = 23 := by
      rw [Fin.sum_univ_four]
      change 0 + 0 + 14 + 9 = 23
      decide
    have hzsq : (∑ i, (((![0, 0, 14, 9] : Fin 4 → ℕ) i : ℤ)^2)) = 277 := by
      rw [Fin.sum_univ_four]
      change (0 : ℤ)^2 + 0^2 + 14^2 + 9^2 = 277
      decide
    unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
    simp only [hzsum, hzsq]
    fin_cases Q <;> norm_num
  · intro _Q
    exact cells_14_09
#print axioms Paper7MomentBlock00.valid_14_09

def qvalues_14_09 : Fin 19 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.qvalues_14_09

theorem row_14_09 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨9, by decide⟩⟩) = 10 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨9, by decide⟩⟩) = (![0, 0, 14, 9] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  calc
    b4RowContribution (![0, 0, 14, 9] : Fin 4 → ℕ) =
        sparseRowValue ({13} : Finset (Fin 19)) (fun _ => layers_14_09) :=
      sparseRow_sound (![0, 0, 14, 9] : Fin 4 → ℕ) ({13} : Finset (Fin 19)) (fun _ => layers_14_09) valid_14_09
    _ = 10 := by
      unfold sparseRowValue
      calc
        _ = ∑ Q : Fin 19, qvalues_14_09 Q := by
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
        _ = 10 := by decide
#print axioms Paper7MomentBlock00.row_14_09

theorem row_14_10 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨10, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨10, by decide⟩⟩) = (![0, 0, 14, 10] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 10] : Fin 4 → ℕ) i) = 24 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 10 = 24
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 10] : Fin 4 → ℕ) i : ℤ)^2)) = 296 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 10^2 = 296
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_10

theorem row_14_11 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨11, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨11, by decide⟩⟩) = (![0, 0, 14, 11] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 11] : Fin 4 → ℕ) i) = 25 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 11 = 25
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 11] : Fin 4 → ℕ) i : ℤ)^2)) = 317 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 11^2 = 317
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_11

theorem row_14_12 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨12, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨12, by decide⟩⟩) = (![0, 0, 14, 12] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 12] : Fin 4 → ℕ) i) = 26 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 12 = 26
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 12] : Fin 4 → ℕ) i : ℤ)^2)) = 340 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 12^2 = 340
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_12

theorem row_14_13 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨13, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨13, by decide⟩⟩) = (![0, 0, 14, 13] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 13] : Fin 4 → ℕ) i) = 27 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 13 = 27
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 13] : Fin 4 → ℕ) i : ℤ)^2)) = 365 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 13^2 = 365
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_13

theorem row_14_14 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨14, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨14, by decide⟩⟩) = (![0, 0, 14, 14] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 14] : Fin 4 → ℕ) i) = 28 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 14 = 28
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 14] : Fin 4 → ℕ) i : ℤ)^2)) = 392 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 14^2 = 392
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_14

theorem row_14_15 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩⟩) = (![0, 0, 14, 15] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 15] : Fin 4 → ℕ) i) = 29 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 15 = 29
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 15] : Fin 4 → ℕ) i : ℤ)^2)) = 421 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 15^2 = 421
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_15

theorem row_14_16 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩⟩) = (![0, 0, 14, 16] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 16] : Fin 4 → ℕ) i) = 30 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 16 = 30
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 16] : Fin 4 → ℕ) i : ℤ)^2)) = 452 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 16^2 = 452
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_16

theorem row_14_17 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨17, by decide⟩⟩) = (![0, 0, 14, 17] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 17] : Fin 4 → ℕ) i) = 31 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 17 = 31
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 17] : Fin 4 → ℕ) i : ℤ)^2)) = 485 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 17^2 = 485
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_17

theorem row_14_18 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨18, by decide⟩⟩) = (![0, 0, 14, 18] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 18] : Fin 4 → ℕ) i) = 32 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 18 = 32
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 18] : Fin 4 → ℕ) i : ℤ)^2)) = 520 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 18^2 = 520
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_18

theorem row_14_19 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨19, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨19, by decide⟩⟩) = (![0, 0, 14, 19] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 19] : Fin 4 → ℕ) i) = 33 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 19 = 33
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 19] : Fin 4 → ℕ) i : ℤ)^2)) = 557 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 19^2 = 557
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_19

theorem row_14_20 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨20, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨20, by decide⟩⟩) = (![0, 0, 14, 20] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 20] : Fin 4 → ℕ) i) = 34 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 20 = 34
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 20] : Fin 4 → ℕ) i : ℤ)^2)) = 596 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 20^2 = 596
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_20

theorem row_14_21 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨21, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨21, by decide⟩⟩) = (![0, 0, 14, 21] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 21] : Fin 4 → ℕ) i) = 35 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 21 = 35
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 21] : Fin 4 → ℕ) i : ℤ)^2)) = 637 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 21^2 = 637
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_21

theorem row_14_22 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨22, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨22, by decide⟩⟩) = (![0, 0, 14, 22] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 22] : Fin 4 → ℕ) i) = 36 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 22 = 36
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 22] : Fin 4 → ℕ) i : ℤ)^2)) = 680 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 22^2 = 680
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_22

theorem row_14_23 : b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨23, by decide⟩⟩) = 0 := by
  have hz : (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, ⟨23, by decide⟩⟩) = (![0, 0, 14, 23] : Fin 4 → ℕ) := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  apply rowContribution_zero_of_rejected
  intro Q
  have hzsum : (∑ i, (![0, 0, 14, 23] : Fin 4 → ℕ) i) = 37 := by
    rw [Fin.sum_univ_four]
    change 0 + 0 + 14 + 23 = 37
    decide
  have hzsq : (∑ i, (((![0, 0, 14, 23] : Fin 4 → ℕ) i : ℤ)^2)) = 725 := by
    rw [Fin.sum_univ_four]
    change (0 : ℤ)^2 + 0^2 + 14^2 + 23^2 = 725
    decide
  unfold B4CatalogRowAccept b4Theta b4FeatureCatalog
  simp only [hzsum, hzsq]
  fin_cases Q <;> norm_num
#print axioms Paper7MomentBlock00.row_14_23

def values_14 : Fin 24 → ℕ := ![1, 2, 0, 0, 2, 9, 17, 8, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
#print axioms Paper7MomentBlock00.values_14

theorem column_14 :
    (∑ d : Fin 24, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, d⟩)) = 49 := by
  calc
    (∑ d : Fin 24, b4RowContribution (b4IndexZ ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨14, by decide⟩, d⟩)) =
        ∑ d : Fin 24, values_14 d := by
      apply Finset.sum_congr rfl
      intro d _
      fin_cases d
      · exact row_14_00
      · exact row_14_01
      · exact row_14_02
      · exact row_14_03
      · exact row_14_04
      · exact row_14_05
      · exact row_14_06
      · exact row_14_07
      · exact row_14_08
      · exact row_14_09
      · exact row_14_10
      · exact row_14_11
      · exact row_14_12
      · exact row_14_13
      · exact row_14_14
      · exact row_14_15
      · exact row_14_16
      · exact row_14_17
      · exact row_14_18
      · exact row_14_19
      · exact row_14_20
      · exact row_14_21
      · exact row_14_22
      · exact row_14_23
    _ = 49 := by decide
#print axioms Paper7MomentBlock00.column_14

end Paper7MomentBlock00
