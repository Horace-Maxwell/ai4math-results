import Research.TaskH.Challenge

set_option autoImplicit false

universe u

namespace TaskH

open Challenge SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {k : ℕ}

theorem critical_not_colorable (h : IsCriticalPlus k G) : ¬ G.Colorable k := by
  have hc : G.chromaticNumber = (k : ℕ∞) + 1 := by simpa using h.1
  exact (SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable.mp hc).2

theorem critical_colorable_deletedVertex (h : IsCriticalPlus k G) (v : V) :
    (G.induce {x | x ≠ v}).Colorable k := by
  rw [SimpleGraph.induce_eq_coe_induce_top]
  apply h.2 _
  intro heq
  have hmem : v ∈ ((⊤ : G.Subgraph).induce {x | x ≠ v}).verts := by
    rw [heq]
    exact Set.mem_univ v
  exact hmem rfl

theorem critical_colorable_deletedEdge (h : IsCriticalPlus k G)
    {x y : V} (hxy : G.Adj x y) :
    (G.deleteEdges {s(x, y)}).Colorable k := by
  let S : G.Subgraph := (⊤ : G.Subgraph).deleteEdges {s(x, y)}
  have hS : S ≠ ⊤ := by
    intro heq
    have ha : S.Adj x y := by
      rw [heq]
      exact hxy
    change G.Adj x y ∧ s(x, y) ∉ ({s(x, y)} : Set (Sym2 V)) at ha
    exact ha.2 (Set.mem_singleton _)
  obtain ⟨c⟩ := h.2 S hS
  refine ⟨SimpleGraph.Coloring.mk (fun z => c ⟨z, Set.mem_univ z⟩) ?_⟩
  intro a b hab
  apply c.valid
  exact SimpleGraph.deleteEdges_adj.mp hab

theorem deletedEdge_coloring_endpoints (h : IsCriticalPlus k G)
    {x y : V} (c : (G.deleteEdges {s(x, y)}).Coloring (Fin k)) :
    c x = c y := by
  classical
  by_contra hne
  apply critical_not_colorable h
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro a b hab
  by_cases he : s(a, b) = s(x, y)
  · have hp : (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
      simpa only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] using he
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne
    · exact Ne.symm hne
  · apply c.valid
    exact SimpleGraph.deleteEdges_adj.mpr ⟨hab, by simpa using he⟩

#print axioms critical_not_colorable
#print axioms critical_colorable_deletedVertex
#print axioms critical_colorable_deletedEdge
#print axioms deletedEdge_coloring_endpoints

end TaskH
