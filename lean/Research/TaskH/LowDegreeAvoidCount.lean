import Research.TaskH.LowDegreeAvoidCycles
import Research.TaskH.LowDegreeCycleCount

/-!
The original count fifteen, together with the twelve actual cycles through
a degree-four vertex, leaves precisely three cycles avoiding that vertex.
The three color orders distinguish them even when base vertices differ.
Consequently each order's canonical cycle contains all four neighbors.
-/

set_option autoImplicit false

universe u

namespace TaskH

open Challenge SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

theorem follows_rotate_degreeFour [DecidableEq V] {x : V} (p : G.Walk x x)
    (y : V) (hy : y ∈ p.support) (c : V → Fin 4) (j : Fin 3)
    (hf : Follows p c (fourColorCycle j)) :
    Follows (p.rotate y hy) c (fourColorCycle j) := by
  intro d hd
  exact hf d ((p.rotate_darts y hy).perm.mem_iff.mp hd)

/-- The representatives distinguish undirected cycles independently of the
chosen base vertex. The labels here are the actual common deleted colors. -/
theorem follows_four_cycles_index_eq_anybase [DecidableEq V] {x y : V}
    {p : G.Walk x x} {q : G.Walk y y}
    (hp : p.IsCycle) (hq : q.IsCycle) (hl : p.length = 4)
    (c : V → Fin 4) (i j : Fin 3)
    (hpi : Follows p c (fourColorCycle i)) (hqj : Follows q c (fourColorCycle j))
    (he : p.edges.toFinset = q.edges.toFinset) : i = j := by
  obtain ⟨hy, _⟩ := CycleOrientation.cycle_eq_rotate_or_reverse_of_toFinset_eq hp hq he
  apply follows_four_cycles_index_eq ((Walk.isCycle_rotate hy).mpr hp) hq
    (by simpa only [Walk.length_rotate] using hl) c i j
    (follows_rotate_degreeFour p y hy c i hpi) hqj
  exact (Basics.rotate_edges_toFinset p y hy).trans he

def degreeFourAvoidingEdges (G : SimpleGraph V) (v : V) : Set (Finset (Sym2 V)) :=
  {s | s ∈ ModCycleEdgeSets 4 G ∧ ¬ CycleContains s v}

section FiniteGraph

variable [Fintype V] [DecidableRel G.Adj]

theorem degreeFourAvoidCycle_mem (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) :
    (degreeFourAvoidCycle hcrit hs v c hdegree i j).edges.toFinset ∈
      degreeFourAvoidingEdges G v := by
  classical
  have hp := degreeFourAvoidCycle_isCycle hcrit hs v c hdegree i j
  refine ⟨(Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr ?_, ?_⟩
  · simpa only [degreeFourAvoidCycle_length] using (dvd_refl 4)
  · intro hv
    exact degreeFourAvoidCycle_avoids hcrit hs v c hdegree i j
      ((cycleContains_edges_toFinset_iff _ hp.not_nil v).mp hv)

theorem degreeFourAvoidCycle_order_eq (hcrit : IsCriticalPlus 4 G)
    (hs : ShortFourCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i i' : Fin 4) (j j' : Fin 3)
    (he : (degreeFourAvoidCycle hcrit hs v c hdegree i j).edges.toFinset =
      (degreeFourAvoidCycle hcrit hs v c hdegree i' j').edges.toFinset) : j = j' := by
  classical
  exact follows_four_cycles_index_eq_anybase
    (degreeFourAvoidCycle_isCycle hcrit hs v c hdegree i j)
    (degreeFourAvoidCycle_isCycle hcrit hs v c hdegree i' j')
    (degreeFourAvoidCycle_length hcrit hs v c hdegree i j)
    (deletedColorExtension v c) j j'
    (degreeFourAvoidCycle_follows hcrit hs v c hdegree i j)
    (degreeFourAvoidCycle_follows hcrit hs v c hdegree i' j') he

theorem degreeFourAvoidCycle_order_injective (hcrit : IsCriticalPlus 4 G)
    (hs : ShortFourCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) : Function.Injective (fun j : Fin 3 =>
      (degreeFourAvoidCycle hcrit hs v c hdegree i j).edges.toFinset) := by
  intro j j' he
  exact degreeFourAvoidCycle_order_eq hcrit hs v c hdegree i i j j' he

theorem degreeFour_avoiding_budget (hcrit : IsCriticalPlus 4 G)
    (hs : ShortFourCycles G) (hcount : modCycleCount 4 G = 15) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4) :
    (degreeFourAvoidingEdges G v).ncard ≤ 3 := by
  classical
  let T : Set (Finset (Sym2 V)) :=
    {s | s ∈ ModCycleEdgeSets 4 G ∧ CycleContains s v}
  have hsub : T ⊆ ModCycleEdgeSets 4 G := fun _ h => h.1
  have hpart : ModCycleEdgeSets 4 G \ T = degreeFourAvoidingEdges G v := by
    ext s
    change (s ∈ ModCycleEdgeSets 4 G ∧ ¬ (s ∈ ModCycleEdgeSets 4 G ∧
      CycleContains s v)) ↔ (s ∈ ModCycleEdgeSets 4 G ∧ ¬ CycleContains s v)
    tauto
  have hsum := Set.ncard_sdiff_add_ncard_of_subset hsub
    (Basics.modCycleEdgeSets_finite 4 G)
  rw [hpart] at hsum
  change (ModCycleEdgeSets 4 G).ncard = 15 at hcount
  have hthrough : 12 ≤ T.ncard := degreeFour_twelve_cycles_through hcrit hs v c hdegree
  omega

/-- The three actual cycles based at color zero exhaust all avoiding cycles. -/
theorem degreeFour_avoiding_exhausted (hcrit : IsCriticalPlus 4 G)
    (hs : ShortFourCycles G) (hcount : modCycleCount 4 G = 15) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4) :
    Set.range (fun j : Fin 3 =>
      (degreeFourAvoidCycle hcrit hs v c hdegree 0 j).edges.toFinset) =
        degreeFourAvoidingEdges G v := by
  classical
  let E : Fin 3 → Finset (Sym2 V) := fun j =>
    (degreeFourAvoidCycle hcrit hs v c hdegree 0 j).edges.toFinset
  have hsub : Set.range E ⊆ degreeFourAvoidingEdges G v := by
    rintro s ⟨j, rfl⟩
    exact degreeFourAvoidCycle_mem hcrit hs v c hdegree 0 j
  have hcard : (Set.range E).ncard = 3 := by
    rw [Set.ncard_range_of_injective (degreeFourAvoidCycle_order_injective
      hcrit hs v c hdegree 0)]
    exact Nat.card_fin 3
  apply Set.eq_of_subset_of_ncard_le hsub
  rw [hcard]
  exact degreeFour_avoiding_budget hcrit hs hcount v c hdegree

theorem degreeFourAvoidCycle_edges_eq (hcrit : IsCriticalPlus 4 G)
    (hs : ShortFourCycles G) (hcount : modCycleCount 4 G = 15) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) :
    (degreeFourAvoidCycle hcrit hs v c hdegree i j).edges.toFinset =
      (degreeFourAvoidCycle hcrit hs v c hdegree 0 j).edges.toFinset := by
  have hm := degreeFourAvoidCycle_mem hcrit hs v c hdegree i j
  rw [← degreeFour_avoiding_exhausted hcrit hs hcount v c hdegree] at hm
  obtain ⟨j', he⟩ := hm
  have hj : j' = j := degreeFourAvoidCycle_order_eq hcrit hs v c hdegree 0 i j' j he
  subst j'
  exact he.symm

theorem degreeFourAvoidCycle_contains_neighbors (hcrit : IsCriticalPlus 4 G)
    (hs : ShortFourCycles G) (hcount : modCycleCount 4 G = 15) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) :
    (degreeFourNeighbor hcrit v c hdegree i).val ∈
      (degreeFourAvoidCycle hcrit hs v c hdegree 0 j).support := by
  classical
  apply (cycleContains_edges_toFinset_iff _
    (degreeFourAvoidCycle_isCycle hcrit hs v c hdegree 0 j).not_nil _).mp
  rw [← degreeFourAvoidCycle_edges_eq hcrit hs hcount v c hdegree i j]
  exact (cycleContains_edges_toFinset_iff _
    (degreeFourAvoidCycle_isCycle hcrit hs v c hdegree i j).not_nil _).mpr
      (degreeFourAvoidCycle hcrit hs v c hdegree i j).start_mem_support

end FiniteGraph

end TaskH

#print axioms TaskH.follows_four_cycles_index_eq_anybase
#print axioms TaskH.degreeFour_avoiding_budget
#print axioms TaskH.degreeFour_avoiding_exhausted
#print axioms TaskH.degreeFourAvoidCycle_contains_neighbors
