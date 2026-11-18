import Research.TaskH.Fan.RootedSetRetraction

/-!
Actual interiors of components of G-b. Connectivity transport is used only
for reachability, never to preserve a prescribed path length. This source
does not assume a block decomposition or a terminal-block existence theorem.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

def deletedInterior (G : SimpleGraph V) (b : V)
    (C : (G.induce {v | v ≠ b}).ConnectedComponent) : Set V :=
  {v | ∃ h : v ≠ b, (⟨v, h⟩ : {w : V // w ≠ b}) ∈ C.supp}

def fragmentBlock (I : Set V) (b : V) : Set V := {v | v = b ∨ v ∈ I}

theorem deletedInterior_root_not_mem (G : SimpleGraph V) (b : V)
    (C : (G.induce {v | v ≠ b}).ConnectedComponent) : b ∉ deletedInterior G b C := by
  rintro ⟨hb, _⟩
  exact hb rfl

theorem deletedInterior_nonempty (G : SimpleGraph V) (b : V)
    (C : (G.induce {v | v ≠ b}).ConnectedComponent) :
    (deletedInterior G b C).Nonempty := by
  obtain ⟨v, hv⟩ := C.nonempty_supp
  exact ⟨v.1, v.2, hv⟩

theorem deletedInterior_closed (G : SimpleGraph V) (b : V)
    (C : (G.induce {v | v ≠ b}).ConnectedComponent) :
    ∀ a ∈ deletedInterior G b C, ∀ d, G.Adj a d →
      d = b ∨ d ∈ deletedInterior G b C := by
  intro a ha d hadj
  obtain ⟨ha', haC⟩ := ha
  by_cases hd : d = b
  · exact Or.inl hd
  · exact Or.inr ⟨hd, C.mem_supp_of_adj_mem_supp haC hadj⟩

theorem fragmentBlock_closed (G : SimpleGraph V) (I : Set V) (b : V)
    (hc : ∀ a ∈ I, ∀ d, G.Adj a d → d = b ∨ d ∈ I) :
    ∀ a ∈ fragmentBlock I b, a ≠ b → ∀ d, G.Adj a d →
      d ∈ fragmentBlock I b := by
  intro a ha hab d hadj
  rcases ha with ha | ha
  · exact False.elim (hab ha)
  · exact hc a ha d hadj

theorem fragment_complement_connected (G : SimpleGraph V) (I : Set V) (b : V)
    (hb : b ∉ I)
    (hc : ∀ a ∈ I, ∀ d, G.Adj a d → d = b ∨ d ∈ I)
    (hG : G.Connected) : (G.induce {v | v ∉ I}).Connected := by
  apply TaskH.Fan.rootedSet_connected G {v | v ∉ I} b hb
  · intro a ha hab d hadj hd
    rcases hc d hd a hadj.symm with he | he
    · exact hab he
    · exact ha he
  · exact hG

theorem deletedInterior_complement_connected (G : SimpleGraph V) (b : V)
    (C : (G.induce {v | v ≠ b}).ConnectedComponent) (hG : G.Connected) :
    (G.induce {v | v ∉ deletedInterior G b C}).Connected := by
  exact fragment_complement_connected G (deletedInterior G b C) b
    (deletedInterior_root_not_mem G b C) (deletedInterior_closed G b C) hG

theorem deletedInterior_connected (G : SimpleGraph V) (b : V)
    (C : (G.induce {v | v ≠ b}).ConnectedComponent) :
    (G.induce (deletedInterior G b C)).Connected := by
  let f : C → deletedInterior G b C := fun a => ⟨a.1.1, a.1.2, a.2⟩
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨ha, haC⟩ := a.2
    exact ⟨⟨⟨a.1, ha⟩, haC⟩, Subtype.ext rfl⟩
  apply TaskH.Fan.connected_of_surjective_adj_or_eq (G := C.toSimpleGraph) f hf
  · intro a d hadj
    exact Or.inr hadj
  · exact C.connected_toSimpleGraph

theorem deletedBlock_connected (G : SimpleGraph V) (b : V)
    (C : (G.induce {v | v ≠ b}).ConnectedComponent) (hG : G.Connected) :
    (G.induce (fragmentBlock (deletedInterior G b C) b)).Connected := by
  exact TaskH.Fan.rootedSet_connected G (fragmentBlock (deletedInterior G b C) b)
    b (Or.inl rfl) (fragmentBlock_closed G _ b (deletedInterior_closed G b C)) hG

theorem deletedBlock_delete_boundary_connected (G : SimpleGraph V) (b : V)
    (C : (G.induce {v | v ≠ b}).ConnectedComponent) :
    ((G.induce (fragmentBlock (deletedInterior G b C) b)).induce
      {v | v ≠ (⟨b, Or.inl rfl⟩ : fragmentBlock (deletedInterior G b C) b)}).Connected := by
  let B := fragmentBlock (deletedInterior G b C) b
  let br : B := ⟨b, Or.inl rfl⟩
  let f : C → {v : B // v ≠ br} := fun a =>
    ⟨⟨a.1.1, Or.inr ⟨a.1.2, a.2⟩⟩, by
      intro he
      exact a.1.2 (congrArg (fun v : B => v.1) he)⟩
  have hf : Function.Surjective f := by
    intro a
    rcases a.1.2 with ha | ⟨ha, haC⟩
    · exact False.elim (a.2 (Subtype.ext ha))
    · refine ⟨⟨⟨a.1.1, ha⟩, haC⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rfl
  apply TaskH.Fan.connected_of_surjective_adj_or_eq (G := C.toSimpleGraph) f hf
  · intro a d hadj
    exact Or.inr hadj
  · exact C.connected_toSimpleGraph

theorem deletedBlock_neighbor_ncard (G : SimpleGraph V) (b : V)
    (C : (G.induce {v | v ≠ b}).ConnectedComponent)
    (a : V) (ha : a ∈ deletedInterior G b C) :
    (G.neighborSet a).ncard =
      ((G.induce (fragmentBlock (deletedInterior G b C) b)).neighborSet
        ⟨a, Or.inr ha⟩).ncard := by
  have hab : a ≠ b := by
    intro he
    subst a
    exact deletedInterior_root_not_mem G b C ha
  exact TaskH.Fan.rootedSet_neighbor_ncard G _ b
    (fragmentBlock_closed G _ b (deletedInterior_closed G b C))
    ⟨a, Or.inr ha⟩ hab

theorem fragmentBlock_ncard [Fintype V] (I : Set V) (b : V) (hb : b ∉ I) :
    (fragmentBlock I b).ncard = I.ncard + 1 := by
  have he : fragmentBlock I b = insert b I := by
    ext v
    rfl
  rw [he, Set.ncard_insert_of_notMem hb]

#print axioms deletedInterior
#print axioms fragmentBlock
#print axioms deletedInterior_root_not_mem
#print axioms deletedInterior_nonempty
#print axioms deletedInterior_closed
#print axioms fragmentBlock_closed
#print axioms fragment_complement_connected
#print axioms deletedInterior_complement_connected
#print axioms deletedInterior_connected
#print axioms deletedBlock_connected
#print axioms deletedBlock_delete_boundary_connected
#print axioms deletedBlock_neighbor_ncard
#print axioms fragmentBlock_ncard
end TaskH.Gao
