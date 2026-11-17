import Research.TaskH.Five.EdgeCycles

set_option autoImplicit false

universe u

namespace TaskH.Five

open _root_.TaskH.Challenge SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- Different representatives cannot traverse the same based five-cycle in
either direction. This checks twelve finite color words, not graphs. -/
theorem fiveColorCycle_traversal_index_eq (i j : Fin 12) (a : Fin 5)
    (h : (∀ r : Fin 5, (fiveColorCycle i ^ r.val) a = (fiveColorCycle j ^ r.val) a) ∨
      (∀ r : Fin 5, (fiveColorCycle i ^ (5 - r.val)) a = (fiveColorCycle j ^ r.val) a)) :
    i = j := by
  have ht : ∀ (i j : Fin 12) (a : Fin 5),
      ((∀ r : Fin 5, (fiveColorCycle i ^ r.val) a = (fiveColorCycle j ^ r.val) a) ∨
      (∀ r : Fin 5, (fiveColorCycle i ^ (5 - r.val)) a = (fiveColorCycle j ^ r.val) a)) →
      i = j := by decide +kernel
  exact ht i j a h

theorem follows_five_cycles_index_eq [DecidableEq V] {x : V} {p q : G.Walk x x}
    (hp : p.IsCycle) (hq : q.IsCycle) (hl : p.length = 5)
    (c : V → Fin 5) (i j : Fin 12)
    (hpi : Follows p c (fiveColorCycle i)) (hqj : Follows q c (fiveColorCycle j))
    (he : p.edges.toFinset = q.edges.toFinset) : i = j := by
  apply fiveColorCycle_traversal_index_eq i j (c x)
  have hor := CycleOrientation.cycle_eq_or_reverse hp hq
    (CycleOrientation.edgeSet_eq_of_toFinset_eq he)
  rcases hor with hqeq | hqrev
  · left
    intro r
    have hri := follows_getVert p c (fiveColorCycle i) hpi r.val (by omega)
    have hrj := follows_getVert q c (fiveColorCycle j) hqj r.val (by rw [hqeq]; omega)
    rw [hqeq] at hrj
    exact hri.symm.trans hrj
  · right
    intro r
    have hri := follows_getVert p c (fiveColorCycle i) hpi (5 - r.val) (by omega)
    have hrj := follows_getVert q c (fiveColorCycle j) hqj r.val
      (by rw [hqrev, Walk.length_reverse]; omega)
    have hv : q.getVert r.val = p.getVert (5 - r.val) := by
      rw [hqrev, Walk.getVert_reverse, hl]
    exact hri.symm.trans ((congrArg c hv).symm.trans hrj)

end TaskH.Five

#print axioms TaskH.Five.fiveColorCycle_traversal_index_eq
#print axioms TaskH.Five.follows_five_cycles_index_eq
