import Research.TaskV.Stanley.AnchorIncidence

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

abbrev RootedRecords (G : SimpleGraph V) (r : V) := {s : Finset V // rootedRecord G r s}

def vertexRecord (hG : G.IsTree) (r x : V) : RootedRecords G r :=
  ⟨(exists_least_record hG r x).choose,(exists_least_record hG r x).choose_spec.1⟩

theorem mem_vertexRecord (hG : G.IsTree) (r x : V) :
    x ∈ (vertexRecord hG r x).val := (exists_least_record hG r x).choose_spec.2.1

theorem mem_iff_vertexRecord_subset (hG : G.IsTree) (r x : V) (s : RootedRecords G r) :
    x ∈ s.val ↔ (vertexRecord hG r x).val ⊆ s.val :=
  ⟨(exists_least_record hG r x).choose_spec.2.2 s.val s.property,fun h => h (mem_vertexRecord ..)⟩

theorem vertexRecord_bijective (hG : G.IsTree) (r : V) : Function.Bijective (vertexRecord hG r) := by
  classical
  constructor
  · intro x y eq
    by_contra h
    obtain ⟨s,hs,hsep⟩ := exists_separating_record hG r h
    let S : RootedRecords G r := ⟨s,Or.inr hs⟩
    apply hsep
    change x ∈ S.val ↔ y ∈ S.val
    rw [mem_iff_vertexRecord_subset hG r x S, mem_iff_vertexRecord_subset hG r y S, eq]
  · rintro ⟨s,rfl | hs⟩
    · refine ⟨r,Subtype.ext ?_⟩
      rcases (vertexRecord hG r r).property with h | h
      · exact h
      · exact (h.2 (mem_vertexRecord ..)).elim
    · obtain ⟨v⟩ := hs.1.1.nonempty
      obtain ⟨a,ha,b,hb,hab⟩ := connected_crossing (s:=(s : Set V)) hG.connected.preconnected
        v.property hs.2
      refine ⟨a,Subtype.ext ?_⟩
      let t := vertexRecord hG r a
      have inc := (mem_iff_vertexRecord_subset hG r a ⟨s,Or.inr hs⟩).mp ha
      rcases t.property with h | h
      · exact (hs.2 (inc (by rw [show (vertexRecord hG r a).val = univ from h]; exact mem_univ r))).elim
      · exact smaller_record_avoids_tip hG hs h ha hb hab inc (mem_vertexRecord ..)

def vertexRecordEquiv (hG : G.IsTree) (r : V) : V ≃ RootedRecords G r :=
  Equiv.ofBijective _ (vertexRecord_bijective hG r)

variable {W : Type*} [Fintype W] {H : SimpleGraph W}

def liftRecordEquiv (hG : G.IsTree) (hH : H.IsTree) (r : V) (q : W)
    (e : RootedRecords G r ≃ RootedRecords H q) : V ≃ W :=
  (vertexRecordEquiv hG r).trans (e.trans (vertexRecordEquiv hH q).symm)

theorem liftRecordEquiv_mem (hG : G.IsTree) (hH : H.IsTree) (r : V) (q : W)
    (e : RootedRecords G r ≃ RootedRecords H q)
    (he : ∀ a b : RootedRecords G r, a.val ⊆ b.val ↔ (e a).val ⊆ (e b).val)
    (x : V) (s : RootedRecords G r) :
    x ∈ s.val ↔ liftRecordEquiv hG hH r q e x ∈ (e s).val := by
  rw [mem_iff_vertexRecord_subset hG r x s,mem_iff_vertexRecord_subset hH q _ (e s)]
  have e' : vertexRecord hH q (liftRecordEquiv hG hH r q e x) = e (vertexRecord hG r x) :=
    (vertexRecordEquiv hH q).apply_symm_apply _
  rw [e']
  exact he _ _

private theorem record_separates_iff {A : Type*} [Fintype A] {J : SimpleGraph A} (t a b : A) :
    (∃! s : Finset A, awaySide J t s ∧ separates s a b) ↔
    ∃! s : RootedRecords J t, separates s.val a b := by
  constructor
  · rintro ⟨s,⟨hs,hp⟩,hu⟩
    refine ⟨⟨s,Or.inr hs⟩,hp,?_⟩
    rintro ⟨u,rfl | ht⟩ h
    · exact (h (iff_of_true (mem_univ _) (mem_univ _))).elim
    · exact Subtype.ext (hu _ ⟨ht,h⟩)
  · rintro ⟨⟨s,rfl | hs⟩,hp,hu⟩
    · exact (hp (iff_of_true (mem_univ _) (mem_univ _))).elim
    · exact ⟨s,⟨hs,hp⟩,fun u h => congrArg Subtype.val (hu ⟨u,Or.inr h.1⟩ h.2)⟩

theorem reconstruct_core_adj (hG : G.IsTree) (hH : H.IsTree) (r : V) (q : W)
    (e : RootedRecords G r ≃ RootedRecords H q)
    (he : ∀ a b : RootedRecords G r, a.val ⊆ b.val ↔ (e a).val ⊆ (e b).val)
    (x y : V) : G.Adj x y ↔ H.Adj (liftRecordEquiv hG hH r q e x) (liftRecordEquiv hG hH r q e y) := by
  classical
  let f := liftRecordEquiv hG hH r q e
  rw [adjacent_iff_unique_separating_record hG r,adjacent_iff_unique_separating_record hH q,record_separates_iff (J:=G) r x y,record_separates_iff (J:=H) q _ _]
  have sep (s : RootedRecords G r) : separates s.val x y ↔ separates (e s).val (f x) (f y) := by
    unfold separates
    rw [liftRecordEquiv_mem hG hH r q e he x s,liftRecordEquiv_mem hG hH r q e he y s]
  constructor
  · rintro ⟨s,h,hu⟩
    refine ⟨e s,(sep s).mp h,?_⟩
    intro t ht
    obtain ⟨t,rfl⟩ := e.surjective t
    exact congrArg e (hu t ((sep t).mpr ht))
  · rintro ⟨t,ht,hu⟩
    obtain ⟨s,rfl⟩ := e.surjective t
    exact ⟨s,(sep s).mpr ht,fun u h => e.injective (hu (e u) ((sep u).mp h))⟩

end
end StanleyContinuation
