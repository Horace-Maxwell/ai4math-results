import Research.TaskH.Five.LowDegreeAvoidCycles
import Research.TaskH.Five.SingletonCycles

/-!
The original count seventy-two, together with the sixty actual cycles through
a degree-four vertex, leaves precisely twelve cycles avoiding that vertex.
The twelve color orders distinguish them even when base vertices differ.
Consequently each order's canonical cycle contains all five neighbors.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open _root_.TaskH.Challenge SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

theorem follows_rotate_degreeFive [DecidableEq V] {x : V} (p : G.Walk x x)
    (y : V) (hy : y ∈ p.support) (c : V → Fin 5) (j : Fin 12)
    (hf : Follows p c (fiveColorCycle j)) :
    Follows (p.rotate y hy) c (fiveColorCycle j) := by
  intro d hd
  exact hf d ((p.rotate_darts y hy).perm.mem_iff.mp hd)

/-- The representatives distinguish undirected cycles independently of the
chosen base vertex. The labels here are the actual common deleted colors. -/
theorem follows_five_cycles_index_eq_anybase [DecidableEq V] {x y : V}
    {p : G.Walk x x} {q : G.Walk y y}
    (hp : p.IsCycle) (hq : q.IsCycle) (hl : p.length = 5)
    (c : V → Fin 5) (i j : Fin 12)
    (hpi : Follows p c (fiveColorCycle i)) (hqj : Follows q c (fiveColorCycle j))
    (he : p.edges.toFinset = q.edges.toFinset) : i = j := by
  obtain ⟨hy, _⟩ := CycleOrientation.cycle_eq_rotate_or_reverse_of_toFinset_eq hp hq he
  apply follows_five_cycles_index_eq ((Walk.isCycle_rotate hy).mpr hp) hq
    (by simpa only [Walk.length_rotate] using hl) c i j
    (follows_rotate_degreeFive p y hy c i hpi) hqj
  exact (Basics.rotate_edges_toFinset p y hy).trans he

def degreeFiveAvoidingEdges (G : SimpleGraph V) (v : V) : Set (Finset (Sym2 V)) :=
  {s | s ∈ ModCycleEdgeSets 5 G ∧ ¬ CycleContains s v}

section FiniteGraph

variable [Fintype V] [DecidableRel G.Adj]

theorem degreeFiveAvoidCycle_mem (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) (j : Fin 12) :
    (degreeFiveAvoidCycle hcrit hs v c hdegree i j).edges.toFinset ∈
      degreeFiveAvoidingEdges G v := by
  classical
  have hp := degreeFiveAvoidCycle_isCycle hcrit hs v c hdegree i j
  refine ⟨(Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr ?_, ?_⟩
  · simpa only [degreeFiveAvoidCycle_length] using (dvd_refl 5)
  · intro hv
    exact degreeFiveAvoidCycle_avoids hcrit hs v c hdegree i j
      ((cycleContains_edges_toFinset_iff _ hp.not_nil v).mp hv)

theorem degreeFiveAvoidCycle_order_eq (hcrit : IsCriticalPlus 5 G)
    (hs : ShortFiveCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i i' : Fin 5) (j j' : Fin 12)
    (he : (degreeFiveAvoidCycle hcrit hs v c hdegree i j).edges.toFinset =
      (degreeFiveAvoidCycle hcrit hs v c hdegree i' j').edges.toFinset) : j = j' := by
  classical
  exact follows_five_cycles_index_eq_anybase
    (degreeFiveAvoidCycle_isCycle hcrit hs v c hdegree i j)
    (degreeFiveAvoidCycle_isCycle hcrit hs v c hdegree i' j')
    (degreeFiveAvoidCycle_length hcrit hs v c hdegree i j)
    (deletedColorExtension v c) j j'
    (degreeFiveAvoidCycle_follows hcrit hs v c hdegree i j)
    (degreeFiveAvoidCycle_follows hcrit hs v c hdegree i' j') he

theorem degreeFiveAvoidCycle_order_injective (hcrit : IsCriticalPlus 5 G)
    (hs : ShortFiveCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) : Function.Injective (fun j : Fin 12 =>
      (degreeFiveAvoidCycle hcrit hs v c hdegree i j).edges.toFinset) := by
  intro j j' he
  exact degreeFiveAvoidCycle_order_eq hcrit hs v c hdegree i i j j' he

theorem degreeFive_avoiding_budget (hcrit : IsCriticalPlus 5 G)
    (hs : ShortFiveCycles G) (hcount : modCycleCount 5 G = 72) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5) :
    (degreeFiveAvoidingEdges G v).ncard ≤ 12 := by
  classical
  let T : Set (Finset (Sym2 V)) :=
    {s | s ∈ ModCycleEdgeSets 5 G ∧ CycleContains s v}
  have hsub : T ⊆ ModCycleEdgeSets 5 G := fun _ h => h.1
  have hpart : ModCycleEdgeSets 5 G \ T = degreeFiveAvoidingEdges G v := by
    ext s
    change (s ∈ ModCycleEdgeSets 5 G ∧ ¬ (s ∈ ModCycleEdgeSets 5 G ∧
      CycleContains s v)) ↔ (s ∈ ModCycleEdgeSets 5 G ∧ ¬ CycleContains s v)
    tauto
  have hsum := Set.ncard_sdiff_add_ncard_of_subset hsub
    (Basics.modCycleEdgeSets_finite 5 G)
  rw [hpart] at hsum
  change (ModCycleEdgeSets 5 G).ncard = 72 at hcount
  have hthrough : 60 ≤ T.ncard := by
    have hsingle := singletonNeighborColors_card_ge hcrit v c
    rw [hdegree] at hsingle
    norm_num at hsingle
    change 60 ≤ (modCyclesThrough 5 G v).ncard
    calc
      60 = 12 * 5 := by norm_num
      _ ≤ 12 * (singletonNeighborColors v c).card := Nat.mul_le_mul_left 12 hsingle
      _ ≤ (modCyclesThrough 5 G v).ncard := singleton_twelve_per_color_cycles hcrit hs v c
  omega

/-- The twelve actual cycles based at color zero exhaust all avoiding cycles. -/
theorem degreeFive_avoiding_exhausted (hcrit : IsCriticalPlus 5 G)
    (hs : ShortFiveCycles G) (hcount : modCycleCount 5 G = 72) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5) :
    Set.range (fun j : Fin 12 =>
      (degreeFiveAvoidCycle hcrit hs v c hdegree 0 j).edges.toFinset) =
        degreeFiveAvoidingEdges G v := by
  classical
  let E : Fin 12 → Finset (Sym2 V) := fun j =>
    (degreeFiveAvoidCycle hcrit hs v c hdegree 0 j).edges.toFinset
  have hsub : Set.range E ⊆ degreeFiveAvoidingEdges G v := by
    rintro s ⟨j, rfl⟩
    exact degreeFiveAvoidCycle_mem hcrit hs v c hdegree 0 j
  have hcard : (Set.range E).ncard = 12 := by
    rw [Set.ncard_range_of_injective (degreeFiveAvoidCycle_order_injective
      hcrit hs v c hdegree 0)]
    exact Nat.card_fin 12
  apply Set.eq_of_subset_of_ncard_le hsub
  rw [hcard]
  exact degreeFive_avoiding_budget hcrit hs hcount v c hdegree

theorem degreeFiveAvoidCycle_edges_eq (hcrit : IsCriticalPlus 5 G)
    (hs : ShortFiveCycles G) (hcount : modCycleCount 5 G = 72) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) (j : Fin 12) :
    (degreeFiveAvoidCycle hcrit hs v c hdegree i j).edges.toFinset =
      (degreeFiveAvoidCycle hcrit hs v c hdegree 0 j).edges.toFinset := by
  have hm := degreeFiveAvoidCycle_mem hcrit hs v c hdegree i j
  rw [← degreeFive_avoiding_exhausted hcrit hs hcount v c hdegree] at hm
  obtain ⟨j', he⟩ := hm
  have hj : j' = j := degreeFiveAvoidCycle_order_eq hcrit hs v c hdegree 0 i j' j he
  subst j'
  exact he.symm

theorem degreeFiveAvoidCycle_contains_neighbors (hcrit : IsCriticalPlus 5 G)
    (hs : ShortFiveCycles G) (hcount : modCycleCount 5 G = 72) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (hdegree : G.degree v = 5)
    (i : Fin 5) (j : Fin 12) :
    (degreeFiveNeighbor hcrit v c hdegree i).val ∈
      (degreeFiveAvoidCycle hcrit hs v c hdegree 0 j).support := by
  classical
  apply (cycleContains_edges_toFinset_iff _
    (degreeFiveAvoidCycle_isCycle hcrit hs v c hdegree 0 j).not_nil _).mp
  rw [← degreeFiveAvoidCycle_edges_eq hcrit hs hcount v c hdegree i j]
  exact (cycleContains_edges_toFinset_iff _
    (degreeFiveAvoidCycle_isCycle hcrit hs v c hdegree i j).not_nil _).mpr
      (degreeFiveAvoidCycle hcrit hs v c hdegree i j).start_mem_support

end FiniteGraph

end TaskH.Five

#print axioms TaskH.Five.follows_rotate_degreeFive
#print axioms TaskH.Five.follows_five_cycles_index_eq_anybase
#print axioms TaskH.Five.degreeFiveAvoidingEdges
#print axioms TaskH.Five.degreeFiveAvoidCycle_mem
#print axioms TaskH.Five.degreeFiveAvoidCycle_order_eq
#print axioms TaskH.Five.degreeFiveAvoidCycle_order_injective
#print axioms TaskH.Five.degreeFive_avoiding_budget
#print axioms TaskH.Five.degreeFive_avoiding_exhausted
#print axioms TaskH.Five.degreeFiveAvoidCycle_edges_eq
#print axioms TaskH.Five.degreeFiveAvoidCycle_contains_neighbors
