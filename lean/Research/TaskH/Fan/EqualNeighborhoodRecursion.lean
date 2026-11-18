import Research.TaskH.Fan.EqualNeighborhoodPathLift

/-! The actual D/full-boundary quotient satisfies all smaller-card IH gates. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem equalNeighborhood_recursive_branch [Fintype V] (G : SimpleGraph V) (x y w u : V)
    (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hfour : ¬rootFourCycleAvoiding G x y) (heq : G.neighborSet y = G.neighborSet x)
    (hw : w ∉ G.neighborSet x) (hwx : w ≠ x) (hwy : w ≠ y)
    (hu : u ∈ equalBranchBoundary G (equalNeighborhoodRegion G x w hw))
    (hdeg : NonrootDegreeAtLeast G x y 3)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (s t : W),
      Fintype.card W < Fintype.card V → RootedTwoConnected J s t →
        NonrootDegreeAtLeast J s t 3 → HasTwoPaths J s t) : HasTwoPaths G x y := by
  classical
  let A := equalBranchDomain G x w hw
  let C := equalBranchCollapsed G x w hw u
  let _ : Fintype A := Fintype.ofFinite _
  let _ : Fintype (IdentificationVertex C) := Fintype.ofFinite _
  let L := equalBranchGraph G x w hw u
  let ur := boundaryRetainedRoot G (equalNeighborhoodRegion G x w hw) u hu
  have hroot : RootedTwoConnected L none (some ur) :=
    equalBranchGraph_rooted G x y w u hG hno heq hw hwx hwy hu
  have hd : NonrootDegreeAtLeast L none (some ur) 3 :=
    equalBranchGraph_nonroot_degree G x y w u hxy hno hfour heq hw hwx hwy hu hdeg
  have hlt : Fintype.card (IdentificationVertex C) < Fintype.card V :=
    equalBranchGraph_card G x y w u hG hno heq hw hwx hwy
  have hL : HasTwoPaths L none (some ur) := ih (IdentificationVertex C) L none (some ur) hlt hroot hd
  exact equalBranch_two_path_lift G x y w u hxy hno heq hw hwx hwy hu hL

theorem counterexample_oriented_rootFour [Fintype V] (G : SimpleGraph V) (x y : V)
    (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hdeg : NonrootDegreeAtLeast G x y 3) (hbad : ¬HasTwoPaths G x y)
    (horient : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (s t : W),
      Fintype.card W < Fintype.card V → RootedTwoConnected J s t →
        NonrootDegreeAtLeast J s t 3 → HasTwoPaths J s t) : rootFourCycleAvoiding G x y := by
  classical
  by_contra hfour
  have heq := counterexample_oriented_equal_neighbors G x y hG hxy hno hfour hdeg hbad horient ih
  have hi := counterexample_neighbor_independent G x y hG hxy hno hbad
  obtain ⟨w, hwX, hwy⟩ := equal_neighbors_exterior_exists G x y hG hxy hno hi hdeg
  have hw : w ∉ G.neighborSet x := fun h => hwX (Or.inr h)
  have hwx : w ≠ x := fun he => hwX (Or.inl he)
  obtain ⟨u, hu, _t, _ht, _hut⟩ := equalBranchBoundary_two G x y w hG hno heq hw hwx hwy
  exact hbad (equalNeighborhood_recursive_branch G x y w u hG hxy hno hfour heq
    hw hwx hwy hu hdeg ih)

#print axioms equalNeighborhood_recursive_branch
#print axioms counterexample_oriented_rootFour
end TaskH.Fan
