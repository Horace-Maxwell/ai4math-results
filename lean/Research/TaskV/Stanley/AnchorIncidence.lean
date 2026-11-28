import Research.TaskV.Stanley.AnchorSides

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Vertex separation does not depend on which side of a split is recorded. -/
def separates (s : Finset V) (x y : V) : Prop := ¬(x ∈ s ↔ y ∈ s)

theorem oriented_cut [DecidableEq V] (r : V) {s : Finset V} (hs : connectedCut G s) :
    ∃ t, awaySide G r t ∧ (t = s ∨ t = sᶜ) := by
  classical
  by_cases h : r ∈ s
  · exact ⟨sᶜ,⟨connectedCut_compl hs,notMem_compl.mpr h⟩,Or.inr rfl⟩
  · exact ⟨s,⟨hs,h⟩,Or.inl rfl⟩

theorem separates_compl [DecidableEq V] (s : Finset V) (x y : V) :
    separates sᶜ x y ↔ separates s x y := by
  classical
  simp only [separates,mem_compl]
  tauto

theorem away_crossing_unique (hG : G.IsTree) {r x y : V} {s t : Finset V}
    (hs : awaySide G r s) (ht : awaySide G r t) (edge : G.Adj x y)
    (hxs : separates s x y) (hxt : separates t x y) : s = t := by
  classical
  have side (u : Finset V) (hu : awaySide G r u) (hsep : separates u x y) (v : V) :
      v ∈ u ↔ ¬((G.deleteEdges {s(x,y)}).Reachable x v ↔
        (G.deleteEdges {s(x,y)}).Reachable x r) := by
    by_cases h : x ∈ u
    · have hy : y ∉ u := fun hh => hsep (iff_of_true h hh)
      have f := fun {z} => cut_membership_by_deleted_edge (s:=(u : Set V)) (x:=z)
        hG.isAcyclic edge h hy hu.1.1.preconnected hu.1.2.preconnected
      simpa [show ¬(G.deleteEdges {s(x,y)}).Reachable x r from fun e => hu.2 (f.mpr e)] using
        (f (z:=v))
    · have hy : y ∈ u := Classical.byContradiction fun hh => hsep (iff_of_false h hh)
      have hc := connectedCut_compl hu.1
      have f := fun {z} => cut_membership_by_deleted_edge (s:=((uᶜ : Finset V) : Set V)) (x:=z)
        hG.isAcyclic edge (mem_compl.mpr h) (notMem_compl.mpr hy) hc.1.preconnected hc.2.preconnected
      have hr : (G.deleteEdges {s(x,y)}).Reachable x r := f.mp (mem_compl.mpr hu.2)
      simp [hr,← f (z:=v)]
  ext v
  exact (side s hs hxs v).trans (side t ht hxt v).symm

theorem exists_separating_record (hG : G.IsTree) (r : V) {x y : V} (ne : x ≠ y) :
    ∃ s, awaySide G r s ∧ separates s x y := by
  classical
  obtain ⟨s,hs,hx,hy,_⟩ := exists_cut_at hG ne
  obtain ⟨t,ht,rfl | rfl⟩ := oriented_cut r hs
  · exact ⟨_,ht,by simp [separates,hx,hy]⟩
  · exact ⟨_,ht,(separates_compl ..).mpr (by simp [separates,hx,hy])⟩

theorem adjacent_iff_unique_separating_record (hG : G.IsTree) (r x y : V) :
    G.Adj x y ↔ ∃! s : Finset V, awaySide G r s ∧ separates s x y := by
  classical
  constructor
  · intro edge
    obtain ⟨s,hs,hxy⟩ := exists_separating_record hG r edge.ne
    exact ⟨s,⟨hs,hxy⟩,fun _ h => away_crossing_unique hG h.1 hs edge h.2 hxy⟩
  · rintro ⟨t,ht,hu⟩
    have ne : x ≠ y := fun e => ht.2 (e ▸ Iff.rfl)
    obtain ⟨sx,csx,hx,hy,b,hb,hxb⟩ := exists_cut_at hG ne
    obtain ⟨sy,csy,hy',hx',a,ha,hya⟩ := exists_cut_at hG ne.symm
    have norm (s : Finset V) (c : connectedCut G s) (sep : separates s x y) :
        t = s ∨ t = sᶜ := by
      obtain ⟨u,au,eu⟩ := oriented_cut r c
      have sep' : separates u x y := by
        rcases eu with rfl | rfl
        · exact sep
        · exact (separates_compl ..).mpr sep
      rw [← hu u ⟨au,sep'⟩]
      exact eu
    have nx := norm sx csx (by simp [separates,hx,hy])
    have ny := norm sy csy (by simp [separates,hx',hy'])
    have e : sx = syᶜ := by
      rcases nx with e | e <;> rcases ny with f | f
      · exact (hx' ((e.symm.trans f) ▸ hx)).elim
      · exact e.symm.trans f
      · simpa using congrArg Compl.compl (e.symm.trans f)
      · have eq : sx = sy := by simpa using congrArg Compl.compl (e.symm.trans f)
        exact (hx' (eq ▸ hx)).elim
    have ah : a ∈ sx := e ▸ mem_compl.mpr ha
    obtain ⟨_,hby⟩ := crossing_edge_unique (s:=(sx : Set V)) hG.isAcyclic hxb hx hb
      hya.symm ah hy csx.1.preconnected csx.2.preconnected
    exact hby ▸ hxb

end
end StanleyContinuation
