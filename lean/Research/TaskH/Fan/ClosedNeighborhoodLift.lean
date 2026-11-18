import Research.TaskH.Fan.RootNeighborhood
import Research.TaskH.Fan.IdentificationPathLift

/-! Every actual simple fresh-root path lifts through a genuine N(x) spoke, then shifts by one. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem closedNeighborhood_path_lift (G : SimpleGraph V) (x : V)
    (y : {v : V // v ∉ closedRootNeighborhood G x})
    (p : (identificationGraph G (closedRootNeighborhood G x)).Walk none (some y))
    (hp : p.IsPath) :
    ∃ P : G.Walk x y.1, P.IsPath ∧ P.length = p.length + 1 := by
  let S := closedRootNeighborhood G x
  obtain ⟨u, h, t, _hcons, ht, hn, hlen⟩ := identification_path_first_spoke G S y p hp
  obtain ⟨s, hs, esu⟩ := h
  have exs : G.Adj x s := by
    rcases hs with hs | hs
    · exact False.elim (u.2 (Or.inr (hs ▸ esu)))
    · exact hs
  obtain ⟨te, hte, hte_len⟩ := identification_exterior_path G S u y t ht hn
  let te' : G.Walk u.1 y.1 :=
    te.map (SimpleGraph.Embedding.induce {v : V | v ∉ S}).toHom
  have hmap : te'.IsPath :=
    (Walk.isPath_map_iff_of_injective Subtype.val_injective).mpr hte
  have hlen' : te'.length = te.length :=
    Walk.length_map (p := te) (f := (SimpleGraph.Embedding.induce {v : V | v ∉ S}).toHom)
  have havoid : ∀ a ∈ S, a ∉ te'.support := by
    intro a ha hm
    change a ∈ (te.map (SimpleGraph.Embedding.induce {v : V | v ∉ S}).toHom).support at hm
    rw [Walk.support_map] at hm
    obtain ⟨b, _hb, he⟩ := List.mem_map.mp hm
    change b.1 = a at he
    exact b.2 (he.symm ▸ ha)
  have hspoke : (Walk.cons esu te').IsPath := hmap.cons (havoid s hs)
  have hx : x ∉ (Walk.cons esu te').support := by
    rw [Walk.support_cons]
    intro hm
    rcases List.mem_cons.mp hm with he | he
    · exact exs.ne he
    · exact havoid x (Or.inl rfl) he
  refine ⟨Walk.cons exs (Walk.cons esu te'), hspoke.cons hx, ?_⟩
  simp only [Walk.length_cons]
  omega

theorem closedNeighborhood_two_path_lift (G : SimpleGraph V) (x : V)
    (y : {v : V // v ∉ closedRootNeighborhood G x})
    (h : HasTwoPaths (identificationGraph G (closedRootNeighborhood G x)) none (some y)) :
    HasTwoPaths G x y.1 := by
  obtain ⟨p, q, hp, hq, hp2, hq2, hgap⟩ := h
  obtain ⟨P, hP, hPlen⟩ := closedNeighborhood_path_lift G x y p hp
  obtain ⟨Q, hQ, hQlen⟩ := closedNeighborhood_path_lift G x y q hq
  refine ⟨P, Q, hP, hQ, ?_, ?_, ?_⟩
  · omega
  · omega
  · rcases hgap with hg | hg
    · left
      omega
    · right
      omega

#print axioms closedNeighborhood_path_lift
#print axioms closedNeighborhood_two_path_lift
end TaskH.Fan
