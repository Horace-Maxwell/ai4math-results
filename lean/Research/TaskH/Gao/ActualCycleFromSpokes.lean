import Research.TaskH.Gao.PathConcatenation

/-! Two actual spokes and an actual avoiding simple path form a genuine cycle.
The component wrapper chooses its path inside the actual deleted component. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem actual_cycle_from_two_spokes (G : SimpleGraph V) (z a b : V)
    (eza : G.Adj z a) (ezb : G.Adj z b) (hab : a ≠ b)
    (p : G.Walk a b) (hp : p.IsPath) (hz : z ∉ p.support) :
    ∃ c : G.Walk z z, c.IsCycle ∧
      ∀ v ∈ c.support, v = z ∨ v ∈ p.support := by
  classical
  let q : G.Walk a z := p.append ezb.symm.toWalk
  have hq : q.IsPath := by
    apply append_isPath_of_only_common_endpoint hp ezb.symm.isPath_toWalk
    intro v hvp hvE
    have hv : v = b ∨ v = z := by
      simpa only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] using hvE
    rcases hv with he | he
    · exact he
    · exact False.elim (hz (Eq.mp (congrArg (fun v : V => v ∈ p.support) he) hvp))
  have hqLen : q.length = p.length + 1 := by
    change (p.append ezb.symm.toWalk).length = p.length + 1
    rw [Walk.length_append]
    rfl
  have hpos : 0 < p.length := (Walk.not_nil_iff_lt_length).mp (Walk.not_nil_of_ne hab)
  let c : G.Walk z z := Walk.cons eza q
  have hcLen : c.length = p.length + 2 := by
    change q.length + 1 = p.length + 2
    rw [hqLen]
  have hc : c.IsCycle := (Walk.isCycle_iff_isPath_tail_and_le_length).mpr
    ⟨(show c.tail.IsPath from by
      change (Walk.cons eza q).tail.IsPath
      rw [Walk.tail_cons]
      exact (Walk.isPath_copy q (Walk.getVert_zero q).symm rfl).mpr hq), by rw [hcLen]; omega⟩
  refine ⟨c, hc, ?_⟩
  intro v hv
  change v ∈ z :: q.support at hv
  rcases List.mem_cons.mp hv with he | hvq
  · exact Or.inl he
  · rcases (Walk.mem_support_append_iff p ezb.symm.toWalk).mp hvq with hvp | hvE
    · exact Or.inr hvp
    · have he : v = b ∨ v = z := by
        simpa only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] using hvE
      rcases he with he | he
      · exact Or.inr (Eq.mpr (congrArg (fun v : V => v ∈ p.support) he) p.end_mem_support)
      · exact Or.inl he

theorem actual_component_two_spokes_cycle (G : SimpleGraph V) (z : V)
    (D : (G.induce {v | v ≠ z}).ConnectedComponent) (a b : D.supp)
    (hab : a ≠ b) (eza : G.Adj z a.1.1) (ezb : G.Adj z b.1.1) :
    ∃ c : G.Walk z z, c.IsCycle ∧
      ∀ v ∈ c.support, v = z ∨ ∃ w : D.supp, w.1.1 = v := by
  classical
  obtain ⟨p, hp⟩ := D.connected_toSimpleGraph.exists_isPath a b
  let f : D.toSimpleGraph →g G :=
    { toFun := fun w => w.1.1, map_rel' := fun e => e }
  have hf : Function.Injective f := by
    intro r s he
    exact Subtype.ext (Subtype.ext he)
  have hab' : a.1.1 ≠ b.1.1 := fun he => hab (hf he)
  have hpath : (p.map f).IsPath := (Walk.isPath_map_iff_of_injective hf).mpr hp
  have havoid : z ∉ (p.map f).support := by
    intro hz
    rw [Walk.support_map] at hz
    obtain ⟨w, _hw, he⟩ := List.mem_map.mp hz
    have he' : w.1.1 = z := he
    exact w.1.2 he'
  obtain ⟨c, hc, hcs⟩ := actual_cycle_from_two_spokes G z a.1.1 b.1.1
    eza ezb hab' (p.map f) hpath havoid
  refine ⟨c, hc, ?_⟩
  intro v hv
  rcases hcs v hv with he | hvm
  · exact Or.inl he
  · rw [Walk.support_map] at hvm
    obtain ⟨w, _hw, he⟩ := List.mem_map.mp hvm
    exact Or.inr ⟨w, he⟩

#print axioms actual_cycle_from_two_spokes
#print axioms actual_component_two_spokes_cycle
end TaskH.Gao
