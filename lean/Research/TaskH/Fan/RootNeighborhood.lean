import Research.TaskH.Fan.RootTriangle
import Research.TaskH.Fan.RootedConnectivity

/-! Actual root-neighborhood data derived internally in the no-four-cycle branch. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

def rootFourCycleAvoiding (G : SimpleGraph V) (x y : V) : Prop :=
  ∃ u w v, x ≠ u ∧ x ≠ w ∧ x ≠ v ∧ u ≠ w ∧ u ≠ v ∧ w ≠ v ∧
    G.Adj x u ∧ G.Adj u w ∧ G.Adj w v ∧ G.Adj v x ∧
      y ∉ ({x, u, w, v} : Set V)

def closedRootNeighborhood (G : SimpleGraph V) (x : V) : Set V :=
  {w | w = x ∨ G.Adj x w}

theorem noFour_neighbor_unique (G : SimpleGraph V) (x y : V) (hxy : x ≠ y)
    (hno : ¬G.Adj x y) (hfour : ¬rootFourCycleAvoiding G x y)
    (w : V) (hwx : w ≠ x) (hwy : w ≠ y) {u v : V}
    (hu : G.Adj x u) (hv : G.Adj x v) (ewu : G.Adj w u) (ewv : G.Adj w v) : u = v := by
  classical
  by_contra huv
  have huy : u ≠ y := fun he => hno (he ▸ hu)
  have hvy : v ≠ y := fun he => hno (he ▸ hv)
  apply hfour
  refine ⟨u, w, v, hu.ne, hwx.symm, hv.ne, ewu.ne.symm, huv, ewv.ne,
    hu, ewu.symm, ewv, hv.symm, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro (h | h | h | h)
  · exact hxy h.symm
  · exact huy h.symm
  · exact hwy h.symm
  · exact hvy h.symm

theorem noFour_closed_neighbors_unique (G : SimpleGraph V) (x y : V) (hxy : x ≠ y)
    (hno : ¬G.Adj x y) (hfour : ¬rootFourCycleAvoiding G x y)
    (w : V) (hw : w ∉ closedRootNeighborhood G x) (hwy : w ≠ y)
    {u v : V} (hu : u ∈ closedRootNeighborhood G x) (hv : v ∈ closedRootNeighborhood G x)
    (ewu : G.Adj w u) (ewv : G.Adj w v) : u = v := by
  have hwx : w ≠ x := fun he => hw (Or.inl he)
  have hu' : G.Adj x u := by
    rcases hu with he | he
    · exact False.elim (hw (Or.inr (he ▸ ewu).symm))
    · exact he
  have hv' : G.Adj x v := by
    rcases hv with he | he
    · exact False.elim (hw (Or.inr (he ▸ ewv).symm))
    · exact he
  exact noFour_neighbor_unique G x y hxy hno hfour w hwx hwy hu' hv' ewu ewv

theorem twoConnected_two_root_neighbors [Fintype V] (G : SimpleGraph V) (hG : TwoConnected G)
    (x y : V) (hxy : x ≠ y) : ∃ u v, u ≠ v ∧ G.Adj x u ∧ G.Adj x v := by
  obtain ⟨p⟩ := hG.2.1 x y
  let u := p.snd
  have eu : G.Adj x u := p.adj_snd (p.not_nil_of_ne hxy)
  obtain ⟨z, hzx, hzu⟩ := exists_vertex_avoiding_two hG.1 x u
  let xr : {w : V // w ≠ u} := ⟨x, eu.ne⟩
  let zr : {w : V // w ≠ u} := ⟨z, hzu⟩
  have hxz : xr ≠ zr := fun he => hzx (congrArg Subtype.val he).symm
  obtain ⟨q⟩ := (hG.2.2 u) xr zr
  have eq : (G.induce {w | w ≠ u}).Adj xr q.snd := q.adj_snd (q.not_nil_of_ne hxz)
  refine ⟨u, q.snd.1, ?_, eu, eq⟩
  exact fun he => q.snd.2 he.symm

theorem closedRootNeighborhood_connected (G : SimpleGraph V) (x : V) :
    (G.induce (closedRootNeighborhood G x)).Connected := by
  let xr : closedRootNeighborhood G x := ⟨x, Or.inl rfl⟩
  have hr : ∀ w : closedRootNeighborhood G x,
      (G.induce (closedRootNeighborhood G x)).Reachable w xr := by
    intro w
    rcases w.2 with he | he
    · have hw : w = xr := Subtype.ext he
      rw [hw]
    · exact (show (G.induce (closedRootNeighborhood G x)).Adj xr w from he).reachable.symm
  refine { preconnected := ?_, nonempty := ⟨xr⟩ }
  intro a b
  exact (hr a).trans (hr b).symm

theorem closedRootNeighborhood_card [Fintype V] (G : SimpleGraph V) (hG : TwoConnected G)
    (x y : V) (hxy : x ≠ y) [Fintype (closedRootNeighborhood G x)] :
    3 ≤ Fintype.card (closedRootNeighborhood G x) := by
  obtain ⟨u, v, huv, eu, ev⟩ := twoConnected_two_root_neighbors G hG x y hxy
  let xr : closedRootNeighborhood G x := ⟨x, Or.inl rfl⟩
  let ur : closedRootNeighborhood G x := ⟨u, Or.inr eu⟩
  let vr : closedRootNeighborhood G x := ⟨v, Or.inr ev⟩
  have hxu : xr ≠ ur := fun he => eu.ne (congrArg Subtype.val he)
  have hxv : xr ≠ vr := fun he => ev.ne (congrArg Subtype.val he)
  have huv' : ur ≠ vr := fun he => huv (congrArg Subtype.val he)
  have hc : 2 < Fintype.card (closedRootNeighborhood G x) :=
    Fintype.two_lt_card_iff.mpr ⟨xr, ur, vr, hxu, hxv, huv'⟩
  omega

theorem closedRootNeighborhood_star (G : SimpleGraph V) (x : V)
    (hi : G.IsIndepSet (G.neighborSet x)) (p q : closedRootNeighborhood G x) :
    (G.induce (closedRootNeighborhood G x)).Adj p q ↔
      (p.1 = x ∧ G.Adj x q.1) ∨ (q.1 = x ∧ G.Adj x p.1) := by
  change G.Adj p.1 q.1 ↔
    (p.1 = x ∧ G.Adj x q.1) ∨ (q.1 = x ∧ G.Adj x p.1)
  constructor
  · intro e
    rcases p.2 with hp | hp
    · refine Or.inl ⟨hp, ?_⟩
      simpa only [hp] using e
    · rcases q.2 with hq | hq
      · refine Or.inr ⟨hq, ?_⟩
        simpa only [hq] using e.symm
      · exact False.elim (hi hp hq e.ne e)
  · rintro (⟨hp, e⟩ | ⟨hq, e⟩)
    · simpa only [hp] using e
    · simpa only [hq] using e.symm

theorem closedRootNeighborhood_other_root_out (G : SimpleGraph V) (x y : V)
    (hxy : x ≠ y) (hno : ¬G.Adj x y) : y ∉ closedRootNeighborhood G x := by
  rintro (hy | hy)
  · exact hxy hy.symm
  · exact hno hy

#print axioms rootFourCycleAvoiding
#print axioms closedRootNeighborhood
#print axioms noFour_neighbor_unique
#print axioms noFour_closed_neighbors_unique
#print axioms twoConnected_two_root_neighbors
#print axioms closedRootNeighborhood_connected
#print axioms closedRootNeighborhood_card
#print axioms closedRootNeighborhood_star
#print axioms closedRootNeighborhood_other_root_out
end TaskH.Fan
