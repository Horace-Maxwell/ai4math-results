import Research.TaskH.Fan.RootedConnectivity

/-!
An actual simple root-to-root path of length at least two follows already
from rooted 2-connectivity. No nonroot degree assumption is needed.
The first real edge is selected in G-y, and the remaining simple path in
G-x is mapped by the actual injective induced embedding before prepending.
-/
set_option autoImplicit false

universe u

namespace TaskH.Fan

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {x y : V}

/-- The original graph has a true x-neighbor other than the other root. -/
theorem rooted_neighbor_avoiding_other [Fintype V]
    (h : RootedTwoConnected G x y) :
    ∃ u : V, G.Adj x u ∧ u ≠ y := by
  obtain ⟨z, hzx, hzy⟩ := exists_vertex_avoiding_two h.2.1 x y
  let a : {v : V // v ≠ y} := ⟨x, h.1⟩
  let b : {v : V // v ≠ y} := ⟨z, hzy⟩
  obtain ⟨p, _hp⟩ := (rooted_delete_right_connected h).exists_isPath a b
  have hab : a ≠ b := by
    intro he
    exact hzx (congrArg Subtype.val he).symm
  obtain ⟨u, hxu, _q, _he⟩ := Walk.exists_eq_cons_of_ne hab p
  exact ⟨u.1, hxu, u.2⟩

/-- Every distinct nonleft root starts a positive simple tail avoiding x. -/
theorem rooted_simple_tail_avoiding_left [Fintype V]
    (h : RootedTwoConnected G x y) (u : V) (hux : u ≠ x) (huy : u ≠ y) :
    ∃ p : G.Walk u y, p.IsPath ∧ 0 < p.length ∧ x ∉ p.support := by
  let a : {v : V // v ≠ x} := ⟨u, hux⟩
  let b : {v : V // v ≠ x} := ⟨y, Ne.symm h.1⟩
  obtain ⟨p, hp⟩ := (rooted_delete_left_connected h).exists_isPath a b
  have hab : a ≠ b := by
    intro he
    exact huy (congrArg Subtype.val he)
  have hpos : 0 < p.length :=
    Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hab)
  let f : G.induce {v : V | v ≠ x} →g G :=
    (SimpleGraph.Embedding.induce {v : V | v ≠ x}).toHom
  have hf : Function.Injective f := Subtype.val_injective
  have hpath : (p.map f).IsPath := (Walk.isPath_map_iff_of_injective hf).mpr hp
  have hlen : (p.map f).length = p.length := Walk.length_map (p := p) (f := f)
  have hpositive : 0 < (p.map f).length := by
    rw [hlen]
    exact hpos
  have havoid : x ∉ (p.map f).support := by
    intro hm
    rw [Walk.support_map] at hm
    rcases List.mem_map.mp hm with ⟨v, _hv, he⟩
    change v.1 = x at he
    exact v.2 he
  exact ⟨p.map f, hpath, hpositive, havoid⟩

/-- Both root-deleted connectivity clauses give a genuine length-at-least-two path. -/
theorem rooted_exists_long_simple_path [Fintype V]
    (h : RootedTwoConnected G x y) :
    ∃ p : G.Walk x y, p.IsPath ∧ 2 ≤ p.length := by
  obtain ⟨u, hxu, huy⟩ := rooted_neighbor_avoiding_other h
  obtain ⟨p, hp, hpos, havoid⟩ :=
    rooted_simple_tail_avoiding_left h u hxu.ne' huy
  refine ⟨Walk.cons hxu p, hp.cons havoid, ?_⟩
  simp only [Walk.length_cons]
  omega

#print axioms rooted_neighbor_avoiding_other
#print axioms rooted_simple_tail_avoiding_left
#print axioms rooted_exists_long_simple_path

end TaskH.Fan
