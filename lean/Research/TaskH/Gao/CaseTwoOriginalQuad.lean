import Research.TaskH.Gao.CaseTwoLargeYFamily
import Research.TaskH.Gao.CaseTwoEqualNeighborhoodFamily

/-! The original ordinary-counterexample interface forces a real rooted four-cycle. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem case2_original_root_quad [Fintype V] (G : SimpleGraph V) (x y : V) (k : ℕ)
    (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y) (hk : 3 ≤ k)
    (hi : G.IsIndepSet (G.neighborSet x))
    (hdegreeOrder : (G.neighborSet x).ncard ≤ (G.neighborSet y).ncard)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r)
    (hcounterexample : ¬HasAdmissiblePaths G x y k) : Case2RootQuad G x y := by
  classical
  by_contra hquad
  have hyK : y ∉ closedRootNeighborhood G x := by
    rintro (hyx | exy)
    · exact hxy hyx.symm
    · exact hno exy
  let C := (G.induce (closedRootNeighborhood G x)ᶜ).connectedComponentMk ⟨y, hyK⟩
  let N := singletonG1Vertices G (closedRootNeighborhood G x) C
  have hyC : y ∈ N := ⟨hyK, rfl⟩
  by_cases hlarge : 2 ≤ N.ncard
  · exact hcounterexample (case2_large_y_original_family G x y k hG hxy hno (by omega)
      hquad C hyC hlarge hd ih)
  · have hsmall : N.ncard ≤ 1 := by omega
    have hsub := case2_small_component_neighbors_subset G x y hno C hyC hsmall
    have heq : G.neighborSet y = G.neighborSet x :=
      Set.eq_of_subset_of_ncard_le hsub hdegreeOrder
    exact hcounterexample (case2_equal_neighborhood_original_family G x y k hG hxy hno hk
      heq hi hquad hd ih)

#print axioms case2_original_root_quad
end TaskH.Gao
