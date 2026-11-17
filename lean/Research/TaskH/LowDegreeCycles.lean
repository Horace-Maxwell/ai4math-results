import Research.TaskH.LowDegreePaths
import Research.TaskH.EdgeCyclesDistinct

/-!
Actual deleted-edge colorings at a degree-four vertex and the resulting
three actual four-cycles for each assigned color. ShortFourCycles is an
internal hypothesis, to be derived from the original frozen equality case.
-/

set_option autoImplicit false

universe u

namespace TaskH

open Challenge SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

section FiniteGraph

variable [Fintype V] [DecidableRel G.Adj]

/-- Assign color i to v. Its unique old color-i neighbor edge is the only
edge that must be deleted. All other colors are the actual original colors. -/
noncomputable def degreeFourEdgeColoring (hcrit : IsCriticalPlus 4 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) :
    (G.deleteEdges {s(v, (degreeFourNeighbor hcrit v c hdegree i).val)}).Coloring (Fin 4) := by
  classical
  refine SimpleGraph.Coloring.mk (fun x => if hx : x = v then i else c ⟨x, hx⟩) ?_
  intro a b hab
  have hg := (SimpleGraph.deleteEdges_adj.mp hab).1
  have hn : s(a, b) ≠ s(v, (degreeFourNeighbor hcrit v c hdegree i).val) := by
    simpa only [Set.mem_singleton_iff] using (SimpleGraph.deleteEdges_adj.mp hab).2
  by_cases ha : a = v
  · subst a
    have hb : b ≠ v := hg.ne.symm
    simp only [dite_eq_right hb]
    intro he
    have hsel := degreeFourNeighbor_eq_of_color hcrit v c hdegree i ⟨b, hb⟩ hg he.symm
    have hbsel : b = (degreeFourNeighbor hcrit v c hdegree i).val := congrArg Subtype.val hsel
    exact hn (by rw [hbsel])
  · by_cases hb : b = v
    · subst b
      simp only [dite_eq_right ha]
      intro he
      have hsel := degreeFourNeighbor_eq_of_color hcrit v c hdegree i ⟨a, ha⟩ hg.symm he
      have hasel : a = (degreeFourNeighbor hcrit v c hdegree i).val := congrArg Subtype.val hsel
      exact hn (by rw [hasel]; exact Sym2.eq_swap)
    · simp only [dite_eq_right ha, dite_eq_right hb]
      exact c.valid hg

theorem degreeFourEdgeColoring_base (hcrit : IsCriticalPlus 4 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) : degreeFourEdgeColoring hcrit v c hdegree i v = i := by
  classical
  change (if hx : v = v then i else c ⟨v, hx⟩) = i
  exact dite_eq_left rfl

theorem degreeFourEdgeColoring_outside (hcrit : IsCriticalPlus 4 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (x : V) (hx : x ≠ v) :
    degreeFourEdgeColoring hcrit v c hdegree i x = c ⟨x, hx⟩ := by
  classical
  change (if h : x = v then i else c ⟨x, h⟩) = c ⟨x, hx⟩
  exact dite_eq_right hx

theorem degreeFourEdgeColoring_neighbor (hcrit : IsCriticalPlus 4 G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) : degreeFourEdgeColoring hcrit v c hdegree i
      (degreeFourNeighbor hcrit v c hdegree i).val = i := by
  rw [degreeFourEdgeColoring_outside hcrit v c hdegree i _
    (degreeFourNeighbor hcrit v c hdegree i).property]
  exact degreeFourNeighbor_color hcrit v c hdegree i

/-- Each pair (assigned color i, cyclic-order representative j) produces an
actual based four-cycle, not an abstract cycle-count certificate. -/
theorem degreeFour_through_cycle (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) :
    ∃ p : G.Walk v v, p.IsCycle ∧ p.length = 4 ∧
      Follows p (degreeFourEdgeColoring hcrit v c hdegree i) (fourColorCycle j) ∧
      (degreeFourNeighbor hcrit v c hdegree i).val ∉ p.support := by
  exact critical_edge_four_cycle hcrit hs (degreeFourNeighbor_adj hcrit v c hdegree i)
    (degreeFourEdgeColoring hcrit v c hdegree i) j

noncomputable def degreeFourCycle (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) : G.Walk v v :=
  Classical.choose (degreeFour_through_cycle hcrit hs v c hdegree i j)

theorem degreeFourCycle_isCycle (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) : (degreeFourCycle hcrit hs v c hdegree i j).IsCycle :=
  (Classical.choose_spec (degreeFour_through_cycle hcrit hs v c hdegree i j)).1

theorem degreeFourCycle_length (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) : (degreeFourCycle hcrit hs v c hdegree i j).length = 4 :=
  (Classical.choose_spec (degreeFour_through_cycle hcrit hs v c hdegree i j)).2.1

theorem degreeFourCycle_follows (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) :
    Follows (degreeFourCycle hcrit hs v c hdegree i j)
      (degreeFourEdgeColoring hcrit v c hdegree i) (fourColorCycle j) :=
  (Classical.choose_spec (degreeFour_through_cycle hcrit hs v c hdegree i j)).2.2.1

theorem degreeFourCycle_avoids_neighbor (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) : (degreeFourNeighbor hcrit v c hdegree i).val ∉
      (degreeFourCycle hcrit hs v c hdegree i j).support :=
  (Classical.choose_spec (degreeFour_through_cycle hcrit hs v c hdegree i j)).2.2.2

end FiniteGraph

end TaskH

#print axioms TaskH.degreeFourEdgeColoring
#print axioms TaskH.degreeFourEdgeColoring_outside
#print axioms TaskH.degreeFour_through_cycle
#print axioms TaskH.degreeFourCycle_follows
