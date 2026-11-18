import Research.TaskH.Fan.FanFiniteOrder
import Research.TaskH.Fan.FanOrdinaryStep
import Research.TaskH.Fan.RootedCutBranch

/-! Every normalized rooted graph is handled internally by actual deletions. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem fan_nonadjacent_vertex_step [Fintype V] (G : SimpleGraph V) (x y : V)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (s t : W),
      Fintype.card W < Fintype.card V → RootedTwoConnected J s t →
        NonrootDegreeAtLeast J s t 3 → HasTwoPaths J s t)
    (hno : ¬G.Adj x y) (hroot : RootedTwoConnected G x y)
    (hdeg : NonrootDegreeAtLeast G x y 3) : HasTwoPaths G x y := by
  classical
  by_cases hsmall : Fintype.card V ≤ 3
  · have hfour := rooted_degree_order_four G x y hroot hdeg
    omega
  · by_cases hd : ∀ b : V, (G.induce {v : V | v ≠ b}).Connected
    · have hG : TwoConnected G := ⟨hroot.2.1, rooted_original_connected hroot, hd⟩
      exact fan_ordinary_vertex_step G x y hG hroot.1 hno hdeg ih
    · obtain ⟨b, hb⟩ := not_forall.mp hd
      exact rootedCut_vertex_induction_branch G x y b hroot hb hdeg ih

#print axioms fan_nonadjacent_vertex_step
end TaskH.Fan
