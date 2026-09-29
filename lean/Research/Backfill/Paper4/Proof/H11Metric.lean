import Research.HKOTriameter
import Research.Backfill.Paper4.Proof.Readings

/-! True graph distances and all metric assertions used by frozen Remark 5 (ii).
The distance-heredity part is supplied by the separate subset-certificate modules.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4.H11Metric
open BackfillPaper4

instance : DecidableRel Challenge.H11.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ Challenge.h11Edges ∨
    (j.val, i.val) ∈ Challenge.h11Edges))

def distanceTable : List (List ℕ) :=
  [[0, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2],
   [1, 0, 2, 2, 1, 2, 1, 3, 3, 2, 3],
   [1, 2, 0, 2, 1, 2, 3, 1, 3, 2, 3],
   [1, 2, 2, 0, 1, 2, 3, 3, 1, 2, 3],
   [2, 1, 1, 1, 0, 3, 2, 2, 2, 1, 4],
   [1, 2, 2, 2, 3, 0, 3, 3, 3, 4, 1],
   [2, 1, 3, 3, 2, 3, 0, 4, 4, 3, 4],
   [2, 3, 1, 3, 2, 3, 4, 0, 4, 3, 4],
   [2, 3, 3, 1, 2, 3, 4, 4, 0, 3, 4],
   [3, 2, 2, 2, 1, 4, 3, 3, 3, 0, 5],
   [2, 3, 3, 3, 4, 1, 4, 4, 4, 5, 0]]

def D11 (i j : Fin 11) : ℕ := (distanceTable.getD i.val []).getD j.val 0

theorem H11_dist : ∀ x y, Challenge.H11.dist x y = D11 x y :=
  HKOTriameter.dist_eq_of_certificate Challenge.H11 D11
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem H11_connected : Challenge.H11.Connected :=
  HKOTriameter.connected_of_dist Challenge.H11 fun x y hxy => by
    rw [H11_dist]
    revert x y
    decide

theorem diam : Challenge.H11.diam = 5 :=
  HKOTriameter.diam_eq_of_bounds Challenge.H11 H11_connected 5
    (fun u v => by rw [H11_dist]; revert u v; decide)
    9 10 (by rw [H11_dist]; decide)

theorem triameter : Challenge.triameter Challenge.H11 = 12 := by
  have hle : ∀ a b c : Fin 11, D11 a b + D11 a c + D11 b c ≤ 12 := by decide +kernel
  apply le_antisymm
  · unfold Challenge.triameter
    apply Finset.sup_le
    rintro ⟨a, b, c⟩ _
    change Challenge.H11.dist a b + Challenge.H11.dist a c + Challenge.H11.dist b c ≤ 12
    simp only [H11_dist]
    exact hle a b c
  · have h : Challenge.triDist Challenge.H11 6 7 8 = 12 := by
      simp only [Challenge.triDist, H11_dist]
      decide
    calc
      12 = Challenge.triDist Challenge.H11 6 7 8 := h.symm
      _ ≤ Challenge.triameter Challenge.H11 :=
        CodexPaper4.MetricBounds.triDist_le_triameter Challenge.H11 6 7 8

theorem diametral_iff (u v : Fin 11) :
    Challenge.IsDiametral Challenge.H11 u v ↔
      (u = 9 ∧ v = 10) ∨ (u = 10 ∧ v = 9) := by
  simp only [Challenge.IsDiametral, diam, H11_dist]
  revert u v
  decide +kernel

theorem peripheral_iff (u : Fin 11) :
    Challenge.IsPeripheral Challenge.H11 u ↔ u = 9 ∨ u = 10 := by
  rw [CodexPaper4.Readings.peripheral_iff_pair Challenge.H11 H11_connected u]
  unfold Challenge.IsPeripheralPair
  simp only [diametral_iff]
  revert u
  decide

theorem triametral_6_7_8 : Challenge.IsTriametral Challenge.H11 6 7 8 := by
  simp only [Challenge.IsTriametral, triameter, Challenge.triDist, H11_dist]
  decide

theorem not_question3' : ¬ Challenge.Question3' Challenge.H11 := by
  intro h
  have hn : ¬ (Challenge.IsPeripheral Challenge.H11 6 ∨
      Challenge.IsPeripheral Challenge.H11 7 ∨ Challenge.IsPeripheral Challenge.H11 8) := by
    simp only [peripheral_iff]
    decide
  exact hn (h 6 7 8 triametral_6_7_8)

theorem question4 : Challenge.Question4 Challenge.H11 := by
  intro x y hxy
  rcases (diametral_iff x y).mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨6, ?_⟩
    simp only [Challenge.IsTriametral, triameter, Challenge.triDist, H11_dist]
    decide
  · refine ⟨6, ?_⟩
    simp only [Challenge.IsTriametral, triameter, Challenge.triDist, H11_dist]
    decide

theorem metric_facts :
    (∀ u v, Challenge.IsDiametral Challenge.H11 u v ↔
      (u = 9 ∧ v = 10) ∨ (u = 10 ∧ v = 9)) ∧ Challenge.H11.diam = 5 ∧
    Challenge.H11.dist 6 7 = 4 ∧ Challenge.H11.dist 6 8 = 4 ∧ Challenge.H11.dist 7 8 = 4 ∧
    Challenge.triameter Challenge.H11 = 12 ∧
    2 * Challenge.H11.diam < Challenge.triameter Challenge.H11 ∧
    Challenge.IsTriametral Challenge.H11 6 7 8 ∧
    ¬ Challenge.IsPeripheral Challenge.H11 6 ∧ ¬ Challenge.IsPeripheral Challenge.H11 7 ∧
    ¬ Challenge.IsPeripheral Challenge.H11 8 ∧ ¬ Challenge.Question3' Challenge.H11 ∧
    Challenge.Question4 Challenge.H11 ∧ Challenge.IsTriametral Challenge.H11 9 10 6 ∧
    Challenge.IsTriametral Challenge.H11 9 10 7 ∧ Challenge.IsTriametral Challenge.H11 9 10 8 ∧
    Challenge.H11.dist 9 10 = 5 ∧ Challenge.H11.dist 9 6 = 3 ∧ Challenge.H11.dist 10 6 = 4 := by
  refine ⟨diametral_iff, diam, ?_, ?_, ?_, triameter, ?_, triametral_6_7_8,
    ?_, ?_, ?_, not_question3', question4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [Challenge.IsTriametral, Challenge.triDist, triameter, diam,
      H11_dist, peripheral_iff]
  all_goals decide

#print axioms H11_dist
#print axioms H11_connected
#print axioms metric_facts

end CodexPaper4.H11Metric
