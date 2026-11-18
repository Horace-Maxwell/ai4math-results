import Research.TaskH.Fan.SingletonRootComponent
import Research.TaskH.Fan.ClosedNeighborhoodBranch

/-! Singleton quotient component implies actual original neighborhood inclusion and equality. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem singleton_identification_neighbor_subset (G : SimpleGraph V) (x y : V)
    (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hc : (identificationYComponent G (closedRootNeighborhood G x)
      ⟨y, closedRootNeighborhood_other_root_out G x y hxy hno⟩).supp.ncard = 1) :
    G.neighborSet y ⊆ G.neighborSet x := by
  classical
  let X := closedRootNeighborhood G x
  let oy : {v : V // v ∉ X} := ⟨y, closedRootNeighborhood_other_root_out G x y hxy hno⟩
  have hn := singleton_deleted_component_neighbors (identificationGraph G X) none (some oy)
    (by intro he; cases he) hc
  intro w ew
  have hwX : w ∈ X := by
    by_contra hw
    have ek : (identificationGraph G X).Adj (some oy) (some ⟨w, hw⟩) := ew
    have he : (some ⟨w, hw⟩ : IdentificationVertex X) = none := hn _ ek
    cases he
  rcases hwX with hw | hw
  · exact False.elim (hno (hw ▸ ew).symm)
  · exact hw

theorem singleton_identification_equal_neighbors [Fintype V] (G : SimpleGraph V) (x y : V)
    (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hc : (identificationYComponent G (closedRootNeighborhood G x)
      ⟨y, closedRootNeighborhood_other_root_out G x y hxy hno⟩).supp.ncard = 1)
    (horient : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard) :
    G.neighborSet y = G.neighborSet x := by
  exact Set.eq_of_subset_of_ncard_le
    (singleton_identification_neighbor_subset G x y hxy hno hc) horient

theorem counterexample_oriented_equal_neighbors [Fintype V] (G : SimpleGraph V)
    (x y : V) (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hfour : ¬rootFourCycleAvoiding G x y) (hdeg : NonrootDegreeAtLeast G x y 3)
    (hbad : ¬HasTwoPaths G x y)
    (horient : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (s t : W),
      Fintype.card W < Fintype.card V → RootedTwoConnected J s t →
        NonrootDegreeAtLeast J s t 3 → HasTwoPaths J s t) :
    G.neighborSet y = G.neighborSet x := by
  exact singleton_identification_equal_neighbors G x y hxy hno
    (counterexample_closed_component_card_one G x y hG hxy hno hfour hdeg hbad ih) horient

theorem singleton_identification_y_degree_one [Fintype V] (G : SimpleGraph V)
    (x y : V) (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hc : (identificationYComponent G (closedRootNeighborhood G x)
      ⟨y, closedRootNeighborhood_other_root_out G x y hxy hno⟩).supp.ncard = 1) :
    ((identificationGraph G (closedRootNeighborhood G x)).neighborSet
      (some ⟨y, closedRootNeighborhood_other_root_out G x y hxy hno⟩)).ncard = 1 := by
  exact singleton_deleted_component_neighbor_ncard _ none _ (by intro he; cases he)
    (closedNeighborhood_quotient_connected G hG x) hc

#print axioms singleton_identification_neighbor_subset
#print axioms singleton_identification_equal_neighbors
#print axioms counterexample_oriented_equal_neighbors
#print axioms singleton_identification_y_degree_one
end TaskH.Fan
