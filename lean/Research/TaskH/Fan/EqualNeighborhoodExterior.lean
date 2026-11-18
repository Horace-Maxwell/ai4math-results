import Research.TaskH.Fan.EqualRootNeighborhoods

/-! A genuine exterior vertex and the actual component after deleting N(x). -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem equal_neighbors_exterior_exists [Fintype V] (G : SimpleGraph V) (x y : V)
    (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hi : G.IsIndepSet (G.neighborSet x)) (hdeg : NonrootDegreeAtLeast G x y 3) :
    ∃ w : V, w ∉ closedRootNeighborhood G x ∧ w ≠ y := by
  classical
  by_contra hn
  have hcover : ∀ w : V, w ∈ closedRootNeighborhood G x ∨ w = y := by
    intro w
    by_cases hw : w ∈ closedRootNeighborhood G x
    · exact Or.inl hw
    · exact Or.inr (by by_contra hwy; exact hn ⟨w, hw, hwy⟩)
  obtain ⟨u, _, _, eu, _⟩ := twoConnected_two_root_neighbors G hG x y hxy
  have huy : u ≠ y := fun he => hno (he ▸ eu)
  have hsub : G.neighborSet u ⊆ ({x, y} : Set V) := by
    intro w e
    rcases hcover w with hw | hw
    · rcases hw with hw | hw
      · exact Set.mem_insert_iff.mpr (Or.inl hw)
      · exact False.elim (hi eu hw e.ne e)
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hw))
  have hsmall : (G.neighborSet u).ncard ≤ 2 := by
    calc
      (G.neighborSet u).ncard ≤ ({x, y} : Set V).ncard := Set.ncard_le_ncard hsub
      _ = 2 := Set.ncard_pair hxy
  have hlarge := hdeg u eu.ne.symm huy
  omega

def equalNeighborhoodComponent (G : SimpleGraph V) (x w : V) (hw : w ∉ G.neighborSet x) :
    (G.induce (G.neighborSet x)ᶜ).ConnectedComponent :=
  (G.induce (G.neighborSet x)ᶜ).connectedComponentMk ⟨w, hw⟩

def equalNeighborhoodRegion (G : SimpleGraph V) (x w : V) (hw : w ∉ G.neighborSet x) : Set V :=
  {v | ∃ hv : v ∉ G.neighborSet x,
    (⟨v, hv⟩ : {v : V // v ∉ G.neighborSet x}) ∈ (equalNeighborhoodComponent G x w hw).supp}

theorem equalNeighborhoodRegion_root (G : SimpleGraph V) (x w : V)
    (hw : w ∉ G.neighborSet x) : w ∈ equalNeighborhoodRegion G x w hw := ⟨hw, rfl⟩

theorem equalNeighborhoodRegion_avoids_roots (G : SimpleGraph V) (x y w : V)
    (hno : ¬G.Adj x y) (heq : G.neighborSet y = G.neighborSet x)
    (hw : w ∉ G.neighborSet x) (hwx : w ≠ x) (hwy : w ≠ y) :
    x ∉ equalNeighborhoodRegion G x w hw ∧ y ∉ equalNeighborhoodRegion G x w hw := by
  let J := G.induce (G.neighborSet x)ᶜ
  let C := equalNeighborhoodComponent G x w hw
  have hx : x ∉ G.neighborSet x := G.irrefl
  have hy : y ∉ G.neighborSet x := hno
  have ix : ∀ v : {v : V // v ∉ G.neighborSet x}, ¬J.Adj ⟨x, hx⟩ v := by
    intro v e
    exact v.2 e
  have iy : ∀ v : {v : V // v ∉ G.neighborSet x}, ¬J.Adj ⟨y, hy⟩ v := by
    intro v e
    have ev : v.1 ∈ G.neighborSet x :=
      Eq.mp (congrArg (fun S : Set V => v.1 ∈ S) heq)
        (show v.1 ∈ G.neighborSet y from e)
    exact v.2 ev
  constructor
  · rintro ⟨hx', hc⟩
    have hr : J.Reachable ⟨x, hx⟩ ⟨w, hw⟩ := C.reachable_of_mem_supp hc rfl
    have he := reachable_eq_of_isolated J ⟨x, hx⟩ ⟨w, hw⟩ ix hr
    exact hwx (congrArg Subtype.val he).symm
  · rintro ⟨hy', hc⟩
    have hr : J.Reachable ⟨y, hy⟩ ⟨w, hw⟩ := C.reachable_of_mem_supp hc rfl
    have he := reachable_eq_of_isolated J ⟨y, hy⟩ ⟨w, hw⟩ iy hr
    exact hwy (congrArg Subtype.val he).symm

theorem equalNeighborhoodRegion_boundary (G : SimpleGraph V) (x w : V)
    (hw : w ∉ G.neighborSet x) (d : V) (hd : d ∈ equalNeighborhoodRegion G x w hw)
    (s : V) (hs : s ∉ equalNeighborhoodRegion G x w hw) (e : G.Adj d s) :
    s ∈ G.neighborSet x := by
  classical
  by_contra hsn
  obtain ⟨hdn, hdc⟩ := hd
  have hsc := (equalNeighborhoodComponent G x w hw).mem_supp_of_adj_mem_supp hdc
    (show (G.induce (G.neighborSet x)ᶜ).Adj ⟨d, hdn⟩ ⟨s, hsn⟩ from e)
  exact hs ⟨hsn, hsc⟩

theorem equalNeighborhoodRegion_connected (G : SimpleGraph V) (x w : V)
    (hw : w ∉ G.neighborSet x) :
    (G.induce (equalNeighborhoodRegion G x w hw)).Connected := by
  let C := equalNeighborhoodComponent G x w hw
  let D := equalNeighborhoodRegion G x w hw
  let f : C.supp → D := fun v => ⟨v.1.1, ⟨v.1.2, v.2⟩⟩
  have hs : Function.Surjective f := by
    intro v
    obtain ⟨hv, hvc⟩ := v.2
    exact ⟨⟨⟨v.1, hv⟩, hvc⟩, Subtype.ext rfl⟩
  have he : ∀ {a b : C.supp}, C.toSimpleGraph.Adj a b →
      f a = f b ∨ (G.induce D).Adj (f a) (f b) := by
    intro a b e
    exact Or.inr e
  exact connected_of_surjective_adj_or_eq f hs he C.connected_toSimpleGraph

#print axioms equal_neighbors_exterior_exists
#print axioms equalNeighborhoodComponent
#print axioms equalNeighborhoodRegion
#print axioms equalNeighborhoodRegion_root
#print axioms equalNeighborhoodRegion_avoids_roots
#print axioms equalNeighborhoodRegion_boundary
#print axioms equalNeighborhoodRegion_connected
end TaskH.Fan
