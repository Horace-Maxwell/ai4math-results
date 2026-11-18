import Research.TaskH.Fan.Challenge

/-!
Elementary actual-graph connectivity for the frozen rooted two-path target.
The added root edge disappears after deleting either root. The two resulting
connected induced graphs overlap in a real third vertex, giving connectivity
of the original G. No two-path theorem is assumed or asserted here.
-/
set_option autoImplicit false

universe u

namespace TaskH.Fan

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {x y : V}

theorem add_root_edge_induce_delete_left (G : SimpleGraph V) (x y : V) :
    (G ⊔ SimpleGraph.edge x y).induce {v | v ≠ x} = G.induce {v | v ≠ x} := by
  ext a b
  simp only [SimpleGraph.induce_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  constructor
  · rintro (h | h)
    · exact h
    · rcases h.1 with h | h
      · exact (a.property h.1).elim
      · exact (b.property h.2).elim
  · exact Or.inl

theorem add_root_edge_induce_delete_right (G : SimpleGraph V) (x y : V) :
    (G ⊔ SimpleGraph.edge x y).induce {v | v ≠ y} = G.induce {v | v ≠ y} := by
  ext a b
  simp only [SimpleGraph.induce_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  constructor
  · rintro (h | h)
    · exact h
    · rcases h.1 with h | h
      · exact (b.property h.2).elim
      · exact (a.property h.1).elim
  · exact Or.inl

theorem rooted_two_connected_symm [Fintype V] (h : RootedTwoConnected G x y) :
    RootedTwoConnected G y x := by
  refine ⟨Ne.symm h.1, ?_⟩
  rw [SimpleGraph.edge_comm]
  exact h.2

theorem rooted_delete_left_connected [Fintype V] (h : RootedTwoConnected G x y) :
    (G.induce {v | v ≠ x}).Connected := by
  have hz := h.2.2.2 x
  rw [add_root_edge_induce_delete_left G x y] at hz
  exact hz

theorem rooted_delete_right_connected [Fintype V] (h : RootedTwoConnected G x y) :
    (G.induce {v | v ≠ y}).Connected := by
  have hz := h.2.2.2 y
  rw [add_root_edge_induce_delete_right G x y] at hz
  exact hz

theorem exists_vertex_avoiding_two [Fintype V] (hcard : 3 ≤ Fintype.card V) (x y : V) :
    ∃ z : V, z ≠ x ∧ z ≠ y := by
  classical
  have hnot : ¬ (Finset.univ : Finset V) ⊆ {x, y} := by
    intro hs
    have hc := Finset.card_le_card hs
    have hp : ({x, y} : Finset V).card ≤ 2 := Finset.card_le_two
    have hc' : Fintype.card V ≤ ({x, y} : Finset V).card := by
      simpa only [Finset.card_univ] using hc
    omega
  obtain ⟨z, _hz, hz⟩ := Finset.not_subset.mp hnot
  refine ⟨z, ?_, ?_⟩
  · intro he
    exact hz (by simp [he])
  · intro he
    exact hz (by simp [he])

theorem rooted_original_connected [Fintype V] (h : RootedTwoConnected G x y) :
    G.Connected := by
  obtain ⟨z, hzx, hzy⟩ := exists_vertex_avoiding_two h.2.1 x y
  have hleft := rooted_delete_left_connected h
  have hright := rooted_delete_right_connected h
  have hvz : ∀ v : V, G.Reachable v z := by
    intro v
    by_cases hv : v = x
    · subst v
      have hr : (G.induce {w | w ≠ y}).Reachable ⟨x, h.1⟩ ⟨z, hzy⟩ :=
        hright ⟨x, h.1⟩ ⟨z, hzy⟩
      exact hr.map (SimpleGraph.Embedding.induce {w | w ≠ y}).toHom
    · have hr : (G.induce {w | w ≠ x}).Reachable ⟨v, hv⟩ ⟨z, hzx⟩ :=
        hleft ⟨v, hv⟩ ⟨z, hzx⟩
      exact hr.map (SimpleGraph.Embedding.induce {w | w ≠ x}).toHom
  refine { preconnected := ?_, nonempty := ⟨x⟩ }
  intro a b
  exact (hvz a).trans (hvz b).symm

end TaskH.Fan

#print axioms TaskH.Fan.add_root_edge_induce_delete_left
#print axioms TaskH.Fan.add_root_edge_induce_delete_right
#print axioms TaskH.Fan.rooted_two_connected_symm
#print axioms TaskH.Fan.rooted_delete_left_connected
#print axioms TaskH.Fan.rooted_delete_right_connected
#print axioms TaskH.Fan.exists_vertex_avoiding_two
#print axioms TaskH.Fan.rooted_original_connected
