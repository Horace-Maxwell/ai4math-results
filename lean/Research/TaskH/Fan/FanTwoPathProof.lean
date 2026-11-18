import Research.TaskH.Fan.FanRootedStep
import Research.TaskH.Fan.RootEdgeNormalization

/-! Complete candidate proof of the exact original frozen two-path predicate. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
variable {V : Type u}

theorem fan_two_path_claim : TwoPathClaim.{u} := by
  have hmain : ∀ n : ℕ, ∀ (W : Type u) [Fintype W], Fintype.card W = n →
      ∀ (G : SimpleGraph W) (x y : W), RootedTwoConnected G x y →
        NonrootDegreeAtLeast G x y 3 → HasTwoPaths G x y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W inst hcard G x y hroot hdeg
      apply hasTwoPaths_of_rootEdgeDeleted G x y
      apply fan_nonadjacent_vertex_step (rootEdgeDeleted G x y) x y
      · intro U instU J a b hlt hrootJ hdegJ
        have hlt' : Fintype.card U < n := by simpa only [hcard] using hlt
        exact ih (Fintype.card U) hlt' U rfl J a b hrootJ hdegJ
      · exact rootEdgeDeleted_not_adj G x y
      · exact rootEdgeDeleted_rooted_two_connected G x y hroot
      · exact rootEdgeDeleted_nonroot_degree G x y 3 hdeg
  intro W inst G x y hroot hdeg
  exact hmain (Fintype.card W) W rfl G x y hroot hdeg

theorem fan_rooted_two_paths [Fintype V] (G : SimpleGraph V) (x y : V)
    (hroot : RootedTwoConnected G x y) (hdeg : NonrootDegreeAtLeast G x y 3) :
    HasTwoPaths G x y := by
  exact fan_two_path_claim V G x y hroot hdeg

#print axioms fan_two_path_claim
#print axioms fan_rooted_two_paths
end TaskH.Fan
