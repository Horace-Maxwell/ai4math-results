import Research.TaskH.Fan.BoundaryQuotientMap

/-! Actual quotient-root deletion and every retained deletion, without a component oracle. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

def boundaryInteriorVertex (G : SimpleGraph V) (D : Set V) (u : V) (v : D) :
    {a : boundaryDomain G D // a ∉ boundaryCollapse G D u} :=
  ⟨⟨v.1, Or.inl v.2⟩, fun h => h.1.1 v.2⟩

theorem boundaryRetained_connected (G : SimpleGraph V) (D : Set V) (u : V)
    (hu : u ∈ equalBranchBoundary G D) (hD : (G.induce D).Connected) :
    ((G.induce (boundaryDomain G D)).induce (boundaryCollapse G D u)ᶜ).Connected := by
  obtain ⟨d, hd, edu⟩ := hu.2
  let J := (G.induce (boundaryDomain G D)).induce (boundaryCollapse G D u)ᶜ
  let ur := boundaryRetainedRoot G D u hu
  let f : G.induce D →g J :=
    { toFun := boundaryInteriorVertex G D u, map_rel' := fun h => h }
  have hr : ∀ a : {v : boundaryDomain G D // v ∉ boundaryCollapse G D u}, J.Reachable a ur := by
    intro a
    rcases a.1.2 with ha | ha
    · let ad : D := ⟨a.1.1, ha⟩
      have he : f ad = a := Subtype.ext (Subtype.ext rfl)
      obtain ⟨q⟩ := hD ad ⟨d, hd⟩
      have hq : J.Reachable (f ad) (f ⟨d, hd⟩) := (q.map f).reachable
      have ed : J.Adj (f ⟨d, hd⟩) ur := edu
      rw [← he]
      exact hq.trans ed.reachable
    · have hau : a.1.1 = u := by
        by_contra he
        exact a.2 ⟨ha, he⟩
      have he : a = ur := Subtype.ext (Subtype.ext hau)
      rw [he]
  refine { preconnected := ?_, nonempty := ⟨ur⟩ }
  intro a b
  exact (hr a).trans (hr b).symm

theorem boundaryQuotient_delete_none_connected (G : SimpleGraph V) (D : Set V) (u : V)
    (hu : u ∈ equalBranchBoundary G D) (hD : (G.induce D).Connected) :
    (((boundaryQuotient G D u) ⊔ SimpleGraph.edge none (some (boundaryRetainedRoot G D u hu))).induce
      {v : IdentificationVertex (boundaryCollapse G D u) | v ≠ none}).Connected := by
  let f : ((G.induce (boundaryDomain G D)).induce (boundaryCollapse G D u)ᶜ) →g
      (((boundaryQuotient G D u) ⊔ SimpleGraph.edge none (some (boundaryRetainedRoot G D u hu))).induce
        {v : IdentificationVertex (boundaryCollapse G D u) | v ≠ none}) :=
    { toFun := fun a => ⟨some a, by intro he; cases he⟩,
      map_rel' := fun h => Or.inl h }
  have hs : Function.Surjective f := by
    rintro ⟨b, hb⟩
    cases b with
    | none => exact False.elim (hb rfl)
    | some b => exact ⟨b, Subtype.ext rfl⟩
  exact SimpleGraph.Connected.map f hs (boundaryRetained_connected G D u hu hD)

theorem boundaryQuotient_rooted [Fintype V] (G : SimpleGraph V) (D : Set V) (u : V)
    (hu : u ∈ equalBranchBoundary G D) (hD : (G.induce D).Connected)
    (hC : (boundaryCollapse G D u).Nonempty) (hG : TwoConnected G)
    [Fintype (IdentificationVertex (boundaryCollapse G D u))] :
    RootedTwoConnected (boundaryQuotient G D u) none (some (boundaryRetainedRoot G D u hu)) := by
  let ur := boundaryRetainedRoot G D u hu
  obtain ⟨d, hd, _⟩ := hu.2
  let dr := boundaryInteriorVertex G D u (⟨d, hd⟩ : D)
  have hnu : (none : IdentificationVertex (boundaryCollapse G D u)) ≠ some ur := by
    intro he
    cases he
  have hnd : (none : IdentificationVertex (boundaryCollapse G D u)) ≠ some dr := by
    intro he
    cases he
  have hud : (some ur : IdentificationVertex (boundaryCollapse G D u)) ≠ some dr := by
    intro he
    have hv : u = d := congrArg Subtype.val (congrArg Subtype.val (Option.some.inj he))
    exact hu.1 (hv.symm ▸ hd)
  have hcard : 2 < Fintype.card (IdentificationVertex (boundaryCollapse G D u)) :=
    Fintype.two_lt_card_iff.mpr ⟨none, some ur, some dr, hnu, hnd, hud⟩
  have hc : ((boundaryQuotient G D u) ⊔ SimpleGraph.edge none (some ur)).Connected :=
    connected_of_surjective_adj_or_eq (boundaryMap G D u)
      (boundaryMap_surjective G D u hC) (boundaryMap_adj_or_eq G D u hu) hG.2.1
  refine ⟨hnu, ?_⟩
  refine ⟨by omega, hc, ?_⟩
  intro v
  cases v with
  | none => exact boundaryQuotient_delete_none_connected G D u hu hD
  | some r => exact boundaryMap_delete_connected G D u hu hC r (hG.2.2 r.1.1)

theorem equalBranchGraph_rooted [Fintype V] (G : SimpleGraph V) (x y w u : V)
    (hG : TwoConnected G) (hno : ¬G.Adj x y) (heq : G.neighborSet y = G.neighborSet x)
    (hw : w ∉ G.neighborSet x) (hwx : w ≠ x) (hwy : w ≠ y)
    (hu : u ∈ equalBranchBoundary G (equalNeighborhoodRegion G x w hw))
    [Fintype (IdentificationVertex (equalBranchCollapsed G x w hw u))] :
    RootedTwoConnected (equalBranchGraph G x w hw u) none
      (some ⟨(⟨u, Or.inr hu⟩ : equalBranchDomain G x w hw),
        by rintro ⟨_, hne⟩; exact hne rfl⟩) := by
  classical
  exact @boundaryQuotient_rooted V ‹Fintype V› G
    (equalNeighborhoodRegion G x w hw) u hu
    (equalNeighborhoodRegion_connected G x w hw)
    (equalBranchCollapsed_nonempty G x y w u hG hno heq hw hwx hwy) hG
    ‹Fintype (IdentificationVertex (equalBranchCollapsed G x w hw u))›

#print axioms boundaryInteriorVertex
#print axioms boundaryRetained_connected
#print axioms boundaryQuotient_delete_none_connected
#print axioms boundaryQuotient_rooted
#print axioms equalBranchGraph_rooted
end TaskH.Fan
