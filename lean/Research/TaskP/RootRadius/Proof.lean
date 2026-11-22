import Research.TaskP.RootRadius.LowerBound
import Research.TaskP.RootRadius.UpperEstimate

open Filter
open scoped Topology
namespace TaskP.GraphRootRadius.Proof
open Challenge

theorem upper_bound {V : Type*} [Fintype V] [Nonempty V] (B : SimpleGraph V)
    {a : ℕ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, rootRadius (petalJoin a m B) ≤
      (1+ε)*scale a (minimumSize B) (minimumCount B) m := by
  let c := minimumSize B
  let s := minimumCount B
  have hc : 0 < c := by classical exact Nat.succ_pos _
  have hs : 0 < s := minimumCount_pos B
  obtain ⟨E,hE⟩ := normalized_eq_one_delta B
  let : Nonempty (Fin a) := ⟨⟨0,ha⟩⟩
  filter_upwards [roots_upper ha hc hs E hε,eventually_gt_atTop 0] with m h hm
  obtain ⟨z,hz,he⟩ := (attain_graph (petalJoin a m B)).1
  rw [← he]
  specialize h (z+1)
  rw [add_sub_cancel_right] at h
  apply h
  by_cases h0 : z+1 = 0
  · exact Or.inr h0
  · left
    rw [← hE, ← root_equation hm B h0, add_sub_cancel_right]
    exact hz

theorem Attainment : Challenge.Attainment := attainment

theorem GeneralAsymptotic : Challenge.GeneralAsymptotic := by
  intro V _ _ B a ha
  let c := minimumSize B
  let s := minimumCount B
  have hc : 0 < c := by classical exact Nat.succ_pos _
  have hs : 0 < s := minimumCount_pos B
  apply tendsto_order.mpr
  constructor
  · intro l hl
    let ε := (1-l)/2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [lower_bound B ha hε,eventually_gt_atTop 1] with m hm hM
    have hS := scale_pos ha hc hs hM
    have hle := (le_div_iff₀ hS).mpr hm
    exact lt_of_lt_of_le (by dsimp [ε]; linarith) hle
  · intro u hu
    let ε := (u-1)/2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [upper_bound B ha hε,eventually_gt_atTop 1] with m hm hM
    have hS := scale_pos ha hc hs hM
    have hle := (div_le_iff₀ hS).mpr hm
    exact lt_of_le_of_lt hle (by dsimp [ε]; linarith)

theorem FriendshipAsymptotic : Challenge.FriendshipAsymptotic :=
  friendship_of_general GeneralAsymptotic

end TaskP.GraphRootRadius.Proof
