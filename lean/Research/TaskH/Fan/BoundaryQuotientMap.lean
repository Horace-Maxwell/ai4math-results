import Research.TaskH.Fan.EqualNeighborhoodBoundary

/-! Actual full-boundary quotient and its edge-or-equality retraction from the whole graph. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

def boundaryDomain (G : SimpleGraph V) (D : Set V) : Set V := D ∪ equalBranchBoundary G D

def boundaryCollapse (G : SimpleGraph V) (D : Set V) (u : V) : Set (boundaryDomain G D) :=
  {v | v.1 ∈ equalBranchBoundary G D ∧ v.1 ≠ u}

def boundaryQuotient (G : SimpleGraph V) (D : Set V) (u : V) :
    SimpleGraph (IdentificationVertex (boundaryCollapse G D u)) :=
  identificationGraph (G.induce (boundaryDomain G D)) (boundaryCollapse G D u)

def boundaryRetainedRoot (G : SimpleGraph V) (D : Set V) (u : V)
    (hu : u ∈ equalBranchBoundary G D) : {v : boundaryDomain G D // v ∉ boundaryCollapse G D u} :=
  ⟨⟨u, Or.inr hu⟩, by rintro ⟨_, hne⟩; exact hne rfl⟩

noncomputable def boundaryMap (G : SimpleGraph V) (D : Set V) (u : V) :
    V → IdentificationVertex (boundaryCollapse G D u) := by
  classical
  exact fun v => if hv : v ∈ boundaryDomain G D then
    identificationMap (boundaryCollapse G D u) ⟨v, hv⟩ else none

theorem boundaryMap_of_mem (G : SimpleGraph V) (D : Set V) (u v : V)
    (hv : v ∈ boundaryDomain G D) :
    boundaryMap G D u v = identificationMap (boundaryCollapse G D u) ⟨v, hv⟩ := by
  classical
  simp only [boundaryMap, dite_eq_left hv]

theorem boundaryMap_of_not_mem (G : SimpleGraph V) (D : Set V) (u v : V)
    (hv : v ∉ boundaryDomain G D) : boundaryMap G D u v = none := by
  classical
  simp only [boundaryMap, dite_eq_right hv]

theorem boundaryMap_retained (G : SimpleGraph V) (D : Set V) (u : V)
    (r : {v : boundaryDomain G D // v ∉ boundaryCollapse G D u}) :
    boundaryMap G D u r.1.1 = some r := by
  classical
  rw [boundaryMap_of_mem G D u r.1.1 r.1.2]
  simp only [identificationMap, dite_eq_right r.2]

theorem boundaryMap_some_value (G : SimpleGraph V) (D : Set V) (u v : V)
    (r : {a : boundaryDomain G D // a ∉ boundaryCollapse G D u})
    (he : boundaryMap G D u v = some r) : v = r.1.1 := by
  classical
  by_cases hv : v ∈ boundaryDomain G D
  · rw [boundaryMap_of_mem G D u v hv] at he
    by_cases hc : (⟨v, hv⟩ : boundaryDomain G D) ∈ boundaryCollapse G D u
    · have hh : (none : IdentificationVertex (boundaryCollapse G D u)) = some r := by
        simpa only [identificationMap, dite_eq_left hc] using he
      cases hh
    · have hh : (⟨⟨v, hv⟩, hc⟩ : {a : boundaryDomain G D // a ∉ boundaryCollapse G D u}) = r := by
        simpa only [identificationMap, dite_eq_right hc, Option.some.injEq] using he
      exact congrArg Subtype.val (congrArg Subtype.val hh)
  · rw [boundaryMap_of_not_mem G D u v hv] at he
    cases he

theorem boundaryMap_surjective (G : SimpleGraph V) (D : Set V) (u : V)
    (hC : (boundaryCollapse G D u).Nonempty) : Function.Surjective (boundaryMap G D u) := by
  classical
  intro b
  obtain ⟨a, ha⟩ := identification_map_surjective (boundaryCollapse G D u) hC b
  exact ⟨a.1, (boundaryMap_of_mem G D u a.1 a.2).trans ha⟩

theorem boundaryMap_cross (G : SimpleGraph V) (D : Set V) (u : V)
    (hu : u ∈ equalBranchBoundary G D) (a b : V)
    (ha : a ∈ boundaryDomain G D) (hb : b ∉ boundaryDomain G D) (e : G.Adj a b) :
    boundaryMap G D u a = boundaryMap G D u b ∨
      ((boundaryQuotient G D u) ⊔ SimpleGraph.edge none (some (boundaryRetainedRoot G D u hu))).Adj
        (boundaryMap G D u a) (boundaryMap G D u b) := by
  classical
  have hs : a ∈ equalBranchBoundary G D := by
    rcases ha with hd | hs
    · exact False.elim (hb (equalBranchRegion_neighbors_full G D a hd b e))
    · exact hs
  rw [boundaryMap_of_mem G D u a ha, boundaryMap_of_not_mem G D u b hb]
  by_cases hau : a = u
  · subst a
    right
    have hn : (⟨u, ha⟩ : boundaryDomain G D) ∉ boundaryCollapse G D u := by
      rintro ⟨_, hne⟩
      exact hne rfl
    have hm : identificationMap (boundaryCollapse G D u) ⟨u, ha⟩ =
        some (boundaryRetainedRoot G D u hu) := by
      simp only [identificationMap, dite_eq_right hn, boundaryRetainedRoot]
    rw [hm]
    exact Or.inr ((SimpleGraph.edge_adj none (some (boundaryRetainedRoot G D u hu)) _ _).mpr
      ⟨Or.inr ⟨rfl, rfl⟩, by intro he; cases he⟩)
  · left
    have hc : (⟨a, ha⟩ : boundaryDomain G D) ∈ boundaryCollapse G D u := ⟨hs, hau⟩
    simp only [identificationMap, dite_eq_left hc]

theorem boundaryMap_adj_or_eq (G : SimpleGraph V) (D : Set V) (u : V)
    (hu : u ∈ equalBranchBoundary G D) {a b : V} (e : G.Adj a b) :
    boundaryMap G D u a = boundaryMap G D u b ∨
      ((boundaryQuotient G D u) ⊔ SimpleGraph.edge none (some (boundaryRetainedRoot G D u hu))).Adj
        (boundaryMap G D u a) (boundaryMap G D u b) := by
  classical
  by_cases ha : a ∈ boundaryDomain G D
  · by_cases hb : b ∈ boundaryDomain G D
    · rw [boundaryMap_of_mem G D u a ha, boundaryMap_of_mem G D u b hb]
      rcases identification_map_adj_or_eq (G.induce (boundaryDomain G D))
        (boundaryCollapse G D u) (show (G.induce (boundaryDomain G D)).Adj ⟨a, ha⟩ ⟨b, hb⟩ from e)
        with he | he
      · exact Or.inl he
      · exact Or.inr (Or.inl he)
    · exact boundaryMap_cross G D u hu a b ha hb e
  · by_cases hb : b ∈ boundaryDomain G D
    · rcases boundaryMap_cross G D u hu b a hb ha e.symm with he | he
      · exact Or.inl he.symm
      · exact Or.inr he.symm
    · left
      rw [boundaryMap_of_not_mem G D u a ha, boundaryMap_of_not_mem G D u b hb]

theorem boundaryMap_delete_connected (G : SimpleGraph V) (D : Set V) (u : V)
    (hu : u ∈ equalBranchBoundary G D) (hC : (boundaryCollapse G D u).Nonempty)
    (r : {v : boundaryDomain G D // v ∉ boundaryCollapse G D u})
    (hG : (G.induce {v : V | v ≠ r.1.1}).Connected) :
    (((boundaryQuotient G D u) ⊔ SimpleGraph.edge none (some (boundaryRetainedRoot G D u hu))).induce
      {v : IdentificationVertex (boundaryCollapse G D u) | v ≠ some r}).Connected := by
  let f : {v : V // v ≠ r.1.1} →
      {v : IdentificationVertex (boundaryCollapse G D u) // v ≠ some r} := fun a =>
    ⟨boundaryMap G D u a.1, fun he => a.2 (boundaryMap_some_value G D u a.1 r he)⟩
  have hs : Function.Surjective f := by
    intro b
    obtain ⟨a, ha⟩ := boundaryMap_surjective G D u hC b.1
    have har : a ≠ r.1.1 := by
      intro he
      have hb : b.1 = some r := ha.symm.trans (he.symm ▸ boundaryMap_retained G D u r)
      exact b.2 hb
    exact ⟨⟨a, har⟩, Subtype.ext ha⟩
  have hf : ∀ {a b : {v : V // v ≠ r.1.1}}, (G.induce {v : V | v ≠ r.1.1}).Adj a b →
      f a = f b ∨
      (((boundaryQuotient G D u) ⊔ SimpleGraph.edge none (some (boundaryRetainedRoot G D u hu))).induce
        {v : IdentificationVertex (boundaryCollapse G D u) | v ≠ some r}).Adj (f a) (f b) := by
    intro a b e
    rcases boundaryMap_adj_or_eq G D u hu e with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr he
  exact connected_of_surjective_adj_or_eq f hs hf hG

#print axioms boundaryDomain
#print axioms boundaryCollapse
#print axioms boundaryQuotient
#print axioms boundaryRetainedRoot
#print axioms boundaryMap
#print axioms boundaryMap_of_mem
#print axioms boundaryMap_of_not_mem
#print axioms boundaryMap_retained
#print axioms boundaryMap_some_value
#print axioms boundaryMap_surjective
#print axioms boundaryMap_cross
#print axioms boundaryMap_adj_or_eq
#print axioms boundaryMap_delete_connected
end TaskH.Fan
