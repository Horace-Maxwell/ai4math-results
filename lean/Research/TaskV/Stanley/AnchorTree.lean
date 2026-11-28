import Research.TaskV.Stanley.StarBasics

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section

variable {V : Type*} {G : SimpleGraph V}

def induceToDelete (G : SimpleGraph V) (s : Set V) (a b : V) (avoid : ¬(a ∈ s ∧ b ∈ s)) :
    G.induce s →g G.deleteEdges {s(a,b)} where
  toFun := Subtype.val
  map_rel' := by
    intro x y hxy
    refine deleteEdges_adj.mpr ⟨hxy,?_⟩
    simp only [Set.mem_singleton_iff,Sym2.eq_iff]
    intro h
    rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact avoid ⟨h₁ ▸ x.property,h₂ ▸ y.property⟩
    · exact avoid ⟨h₂ ▸ y.property,h₁ ▸ x.property⟩

theorem reach_in_delete_of_same_side {s : Set V} {a b x y : V}
    (avoid : ¬(a ∈ s ∧ b ∈ s)) (hconn : (G.induce s).Preconnected)
    (hx : x ∈ s) (hy : y ∈ s) :
    (G.deleteEdges {s(a,b)}).Reachable x y :=
  (hconn ⟨x,hx⟩ ⟨y,hy⟩).map (induceToDelete G s a b avoid)

theorem cut_membership_by_deleted_edge {s : Set V} {a b x : V}
    (hG : G.IsAcyclic) (edge : G.Adj a b) (ha : a ∈ s) (hb : b ∉ s)
    (connectedSide : (G.induce s).Preconnected)
    (connectedOther : (G.induce sᶜ).Preconnected) :
    x ∈ s ↔ (G.deleteEdges {s(a,b)}).Reachable a x := by
  constructor
  · exact fun hx => reach_in_delete_of_same_side (by tauto) connectedSide ha hx
  · intro hx
    by_contra hn
    have hxb := reach_in_delete_of_same_side (a:=a) (b:=b)
      (s:=sᶜ) (by simpa using fun h : a ∉ s ∧ b ∉ s => h.1 ha) connectedOther hn hb
    exact (isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hG edge)) (hx.trans hxb)

theorem crossing_edge_unique {s : Set V} {a b x y : V}
    (hG : G.IsAcyclic) (edge : G.Adj a b) (ha : a ∈ s) (hb : b ∉ s)
    (xy : G.Adj x y) (hx : x ∈ s) (hy : y ∉ s)
    (conn : (G.induce s).Preconnected) (cconn : (G.induce sᶜ).Preconnected) :
    x=a ∧ y=b := by
  by_contra hn
  have ee : (G.deleteEdges {s(a,b)}).Adj x y := by
    refine deleteEdges_adj.mpr ⟨xy,?_⟩
    simp only [Set.mem_singleton_iff,Sym2.eq_iff]
    rintro (h | ⟨h₁,_⟩)
    · exact hn h
    · exact hb (h₁ ▸ hx)
  exact hy ((cut_membership_by_deleted_edge hG edge ha hb conn cconn).mpr
    (((cut_membership_by_deleted_edge hG edge ha hb conn cconn).mp hx).trans ee.reachable))

theorem connected_crossing {s : Set V} {x y : V} (conn : G.Preconnected)
    (hx : x ∈ s) (hy : y ∉ s) :
    ∃ a ∈ s, ∃ b ∉ s, G.Adj a b := by
  by_contra hn
  push Not at hn
  exact hy (reachable_closed (· ∈ s) (conn x y) hx (fun a b ha ab => by
    by_contra hb
    exact hn a ha b hb ab))

theorem crossing_inside {s t : Set V} (conn : (G.induce t).Preconnected)
    {x y : V} (hxt : x ∈ t) (hxs : x ∈ s) (hyt : y ∈ t) (hys : y ∉ s) :
    ∃ a ∈ t, ∃ b ∈ t, a ∈ s ∧ b ∉ s ∧ G.Adj a b := by
  let q : Set t := {z | z.val ∈ s}
  obtain ⟨a,ha,b,hb,hab⟩ := connected_crossing (s:=q) (x:=⟨x,hxt⟩) (y:=⟨y,hyt⟩) conn hxs hys
  exact ⟨a,a.property,b,b.property,ha,hb,hab⟩

theorem tree_cut_laminar {s t : Set V} (acyclic : G.IsAcyclic)
    (sc : (G.induce s).Preconnected) (sc' : (G.induce sᶜ).Preconnected)
    (tc : (G.induce t).Preconnected) (tc' : (G.induce tᶜ).Preconnected)
    {r x : V} (hrs : r ∉ s) (hrt : r ∉ t) (hxs : x ∈ s) (hxt : x ∈ t) :
    s ⊆ t ∨ t ⊆ s := by
  by_contra hn
  push Not at hn
  obtain ⟨a,has,hat⟩ := Set.not_subset.mp hn.1
  obtain ⟨b,hbt,hbs⟩ := Set.not_subset.mp hn.2
  obtain ⟨u,hut,v,hvt,hus,hvs,huv⟩ := crossing_inside tc hxt hxs hbt hbs
  obtain ⟨w,hwt,z,hzt,hws,hzs,hwz⟩ := crossing_inside (t:=tᶜ) tc' hat has hrt hrs
  obtain ⟨h,_⟩ := crossing_edge_unique acyclic huv hus hvs hwz hws hzs sc sc'
  exact hwt (h ▸ hut)

end
end StanleyContinuation
