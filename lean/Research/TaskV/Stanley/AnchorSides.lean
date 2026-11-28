import Research.TaskV.Stanley.AnchorTree

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def connectedCut (G : SimpleGraph V) (s : Finset V) : Prop :=
  (G.induce (s : Set V)).Connected ∧ (G.induce (s : Set V)ᶜ).Connected

theorem connectedCut_compl [DecidableEq V] {s : Finset V} (h : connectedCut G s) :
    connectedCut G sᶜ := by
  unfold connectedCut at *
  rw [Finset.coe_compl, compl_compl]
  exact h.symm

def awaySide (G : SimpleGraph V) (r : V) (s : Finset V) : Prop :=
  connectedCut G s ∧ r ∉ s

def rootedRecord (G : SimpleGraph V) (r : V) (s : Finset V) : Prop :=
  s = univ ∨ awaySide G r s

omit [Fintype V] in
theorem edge_component_cover (hG : G.Connected) {a b : V} (x : V) :
    (G.deleteEdges {s(a,b)}).Reachable a x ∨ (G.deleteEdges {s(a,b)}).Reachable b x := by
  let D := G.deleteEdges {s(a,b)}
  refine reachable_closed (fun q => D.Reachable a q ∨ D.Reachable b q)
    (hG.preconnected a x) (Or.inl .rfl) ?_
  intro u v hu huv
  by_cases hh : s(u,v) = s(a,b)
  · rcases Sym2.eq_iff.mp hh with ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact Or.inr .rfl
    · exact Or.inl .rfl
  · have hd : D.Adj u v := deleteEdges_adj.mpr ⟨huv,by simpa using hh⟩
    exact hu.imp (·.trans hd.reachable) (·.trans hd.reachable)

theorem exists_cut_at (hG : G.IsTree) {x y : V} (hneq : x ≠ y) :
    ∃ s : Finset V, connectedCut G s ∧ x ∈ s ∧ y ∉ s ∧ ∃ b ∉ s, G.Adj x b := by
  classical
  obtain ⟨p,hp⟩ := hG.connected.exists_isPath x y
  cases p with
  | nil => exact (hneq rfl).elim
  | cons hxb q =>
    rename_i b
    let D := G.deleteEdges {s(x,b)}
    let C := D.connectedComponentMk x
    let B := D.connectedComponentMk b
    have noxb : ¬D.Reachable x b := isBridge_iff.mp
      (isAcyclic_iff_forall_adj_isBridge.mp hG.isAcyclic hxb)
    have xmem : x ∈ C.supp := rfl
    have bmem : b ∈ B.supp := rfl
    have dis (z : V) : z ∈ C.supp ↔ ¬z ∈ B.supp := by
      change D.connectedComponentMk z = D.connectedComponentMk x ↔
        ¬D.connectedComponentMk z = D.connectedComponentMk b
      rw [ConnectedComponent.eq,ConnectedComponent.eq]
      constructor
      · exact fun zx zb => noxb (zx.symm.trans zb)
      · intro h
        rcases edge_component_cover (a:=x) (b:=b) hG.connected z with e | e
        · exact e.symm
        · exact (h e.symm).elim
    have compl : C.suppᶜ = B.supp := by
      ext z
      change z ∉ C.supp ↔ z ∈ B.supp
      rw [dis,not_not]
    have incl (U : Set V) : D.induce U ≤ G.induce U := fun _ _ h => (deleteEdges_adj.mp h).1
    have tail : D.Reachable b _ :=
      reachable_deleteEdges_iff_exists_walk.mpr ⟨q,(Walk.isTrail_cons _ _).mp hp.isTrail |>.2⟩
    have hy : _ ∈ B.supp := ConnectedComponent.sound tail.symm
    refine ⟨C.supp.toFinset,?_,by simpa using xmem,?_,b,?_,hxb⟩
    · unfold connectedCut
      rw [Set.coe_toFinset,compl]
      exact ⟨C.connected_toSimpleGraph.mono (incl _),B.connected_toSimpleGraph.mono (incl _)⟩
    · simpa [dis] using not_not_intro hy
    · simpa [dis] using not_not_intro bmem

omit [Fintype V] in
theorem smaller_record_avoids_tip (hG : G.IsTree) {r a b : V} {s t : Finset V}
    (hs : awaySide G r s) (ht : awaySide G r t) (ha : a ∈ s) (hb : b ∉ s)
    (hab : G.Adj a b) (hts : t ⊆ s) (hat : a ∈ t) : t = s := by
  have hbt : b ∉ t := fun h => hb (hts h)
  ext x
  exact (cut_membership_by_deleted_edge (s:=(t : Set V)) hG.isAcyclic hab hat hbt
      ht.1.1.preconnected ht.1.2.preconnected).trans
    (cut_membership_by_deleted_edge (s:=(s : Set V)) hG.isAcyclic hab ha hb
      hs.1.1.preconnected hs.1.2.preconnected).symm

/-- Each vertex is represented by the least rooted component containing it. -/
theorem exists_least_record (hG : G.IsTree) (r x : V) :
    ∃ s : Finset V, rootedRecord G r s ∧ x ∈ s ∧
      ∀ t, rootedRecord G r t → x ∈ t → s ⊆ t := by
  classical
  by_cases e : x=r
  · refine ⟨univ,Or.inl rfl,mem_univ _,?_⟩
    rintro t (rfl | ht) h
    · exact Subset.rfl
    · exact (ht.2 (e ▸ h)).elim
  · obtain ⟨s,hs,hx,hr,b,hb,hab⟩ := exists_cut_at hG e
    have aw : awaySide G r s := ⟨hs,hr⟩
    refine ⟨s,Or.inr aw,hx,?_⟩
    rintro t (rfl | ht) h
    · exact subset_univ _
    rcases tree_cut_laminar (s:=(s : Set V)) (t:=(t : Set V)) hG.isAcyclic
      hs.1.preconnected hs.2.preconnected ht.1.1.preconnected ht.1.2.preconnected
      hr ht.2 hx h with p | p
    · exact p
    · rw [smaller_record_avoids_tip hG aw ht hx hb hab p h]

end
end StanleyContinuation
