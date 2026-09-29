import Research.HKOTriameter
import Research.Backfill.Paper4.Proof.Readings

/-! Complete frozen Remark 4 (3), using an explicit distance certificate for HKO Figure 2.
The table is checked through the general graph-distance soundness theorem.
Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4
namespace HKOFig2Proof

local instance : DecidableRel Challenge.HKOFig2.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ Challenge.hkoFig2Edges ∨
    (j.val, i.val) ∈ Challenge.hkoFig2Edges))

def distanceTable : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 1, 2, 3, 1, 2, 3],
   [1, 0, 1, 2, 3, 4, 2, 3, 4, 2, 3, 4],
   [2, 1, 0, 1, 2, 3, 3, 4, 3, 3, 4, 3],
   [3, 2, 1, 0, 1, 2, 4, 3, 2, 4, 3, 2],
   [4, 3, 2, 1, 0, 1, 3, 2, 1, 3, 2, 1],
   [5, 4, 3, 2, 1, 0, 4, 3, 2, 4, 3, 2],
   [1, 2, 3, 4, 3, 4, 0, 1, 2, 2, 3, 4],
   [2, 3, 4, 3, 2, 3, 1, 0, 1, 3, 4, 3],
   [3, 4, 3, 2, 1, 2, 2, 1, 0, 4, 3, 2],
   [1, 2, 3, 4, 3, 4, 2, 3, 4, 0, 1, 2],
   [2, 3, 4, 3, 2, 3, 3, 4, 3, 1, 0, 1],
   [3, 4, 3, 2, 1, 2, 4, 3, 2, 2, 1, 0]]

def D (i j : Fin 12) : ℕ := (distanceTable.getD i.val []).getD j.val 0

theorem dist : ∀ x y, Challenge.HKOFig2.dist x y = D x y :=
  HKOTriameter.dist_eq_of_certificate Challenge.HKOFig2 D
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem connected : Challenge.HKOFig2.Connected :=
  HKOTriameter.connected_of_dist Challenge.HKOFig2 fun x y hxy => by
    rw [dist]
    revert x y
    decide

theorem diam : Challenge.HKOFig2.diam = 5 :=
  HKOTriameter.diam_eq_of_bounds Challenge.HKOFig2 connected 5
    (fun u v => by rw [dist]; revert u v; decide) 0 5 (by rw [dist]; decide)

theorem triameter : Challenge.triameter Challenge.HKOFig2 = 12 := by
  have hle : ∀ a b c : Fin 12, D a b + D a c + D b c ≤ 12 := by decide +kernel
  apply le_antisymm
  · unfold Challenge.triameter
    apply Finset.sup_le
    rintro ⟨a, b, c⟩ _
    change Challenge.HKOFig2.dist a b + Challenge.HKOFig2.dist a c +
      Challenge.HKOFig2.dist b c ≤ 12
    simp only [dist]
    exact hle a b c
  · have h : Challenge.triDist Challenge.HKOFig2 7 2 10 = 12 := by
      simp only [Challenge.triDist, dist]
      decide
    calc
      12 = Challenge.triDist Challenge.HKOFig2 7 2 10 := h.symm
      _ ≤ Challenge.triameter Challenge.HKOFig2 :=
        MetricBounds.triDist_le_triameter Challenge.HKOFig2 7 2 10

theorem triametral_iff (u v w : Fin 12) :
    Challenge.IsTriametral Challenge.HKOFig2 u v w ↔
      ({u, v, w} : Finset (Fin 12)) = {7, 2, 10} := by
  simp only [Challenge.IsTriametral, triameter, Challenge.triDist, dist]
  revert u v w
  decide +kernel

theorem diametral_iff (u v : Fin 12) :
    Challenge.IsDiametral Challenge.HKOFig2 u v ↔
      (u = 0 ∧ v = 5) ∨ (u = 5 ∧ v = 0) := by
  simp only [Challenge.IsDiametral, diam, dist]
  revert u v
  decide +kernel

theorem no_extension (z : Fin 12) :
    ¬ Challenge.IsTriametral Challenge.HKOFig2 0 5 z := by
  simp only [Challenge.IsTriametral, triameter, Challenge.triDist, dist]
  revert z
  decide

theorem peripheral_iff (u : Fin 12) :
    Challenge.IsPeripheral Challenge.HKOFig2 u ↔ u = 0 ∨ u = 5 := by
  rw [Readings.peripheral_iff_pair Challenge.HKOFig2 connected u]
  unfold Challenge.IsPeripheralPair
  simp only [diametral_iff]
  revert u
  decide

theorem triametral_7_2_10 : Challenge.IsTriametral Challenge.HKOFig2 7 2 10 :=
  (triametral_iff 7 2 10).mpr (by decide)

theorem not_question3 : ¬ Challenge.Question3 Challenge.HKOFig2 := by
  intro h
  have hn : ¬ (Challenge.IsDiametral Challenge.HKOFig2 7 2 ∨
      Challenge.IsDiametral Challenge.HKOFig2 7 10 ∨
      Challenge.IsDiametral Challenge.HKOFig2 2 10) := by
    simp only [diametral_iff]
    decide
  exact hn (h 7 2 10 triametral_7_2_10)

theorem not_question3' : ¬ Challenge.Question3' Challenge.HKOFig2 := by
  intro h
  have hn : ¬ (Challenge.IsPeripheral Challenge.HKOFig2 7 ∨
      Challenge.IsPeripheral Challenge.HKOFig2 2 ∨
      Challenge.IsPeripheral Challenge.HKOFig2 10) := by
    simp only [peripheral_iff]
    decide
  exact hn (h 7 2 10 triametral_7_2_10)

theorem not_question4 : ¬ Challenge.Question4 Challenge.HKOFig2 := by
  intro h
  have hd : Challenge.IsDiametral Challenge.HKOFig2 0 5 :=
    (diametral_iff 0 5).mpr (by decide)
  obtain ⟨z, hz⟩ := h 0 5 hd
  exact no_extension z hz

end HKOFig2Proof

theorem check_Remark4_iii : Challenge.Remark4_iii := by
  refine ⟨HKOFig2Proof.diam, HKOFig2Proof.triameter, HKOFig2Proof.triametral_iff,
    ?_, ?_, ?_, HKOFig2Proof.diametral_iff, HKOFig2Proof.no_extension,
    HKOFig2Proof.peripheral_iff, HKOFig2Proof.not_question3,
    HKOFig2Proof.not_question3', HKOFig2Proof.not_question4⟩
  all_goals rw [HKOFig2Proof.dist]; decide

#print axioms check_Remark4_iii

end CodexPaper4
