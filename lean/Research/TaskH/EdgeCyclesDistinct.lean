import Research.TaskH.EdgeCycles

set_option autoImplicit false

universe u

namespace TaskH

open Challenge SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- Different representatives cannot traverse the same based four-cycle in
either direction. This checks twelve finite color words, not graphs. -/
theorem fourColorCycle_traversal_index_eq (i j : Fin 3) (a : Fin 4)
    (h : (∀ r : Fin 4, (fourColorCycle i ^ r.val) a = (fourColorCycle j ^ r.val) a) ∨
      (∀ r : Fin 4, (fourColorCycle i ^ (4 - r.val)) a = (fourColorCycle j ^ r.val) a)) :
    i = j := by
  have ht : ∀ (i j : Fin 3) (a : Fin 4),
      ((∀ r : Fin 4, (fourColorCycle i ^ r.val) a = (fourColorCycle j ^ r.val) a) ∨
      (∀ r : Fin 4, (fourColorCycle i ^ (4 - r.val)) a = (fourColorCycle j ^ r.val) a)) →
      i = j := by decide +kernel
  exact ht i j a h

theorem follows_four_cycles_index_eq [DecidableEq V] {x : V} {p q : G.Walk x x}
    (hp : p.IsCycle) (hq : q.IsCycle) (hl : p.length = 4)
    (c : V → Fin 4) (i j : Fin 3)
    (hpi : Follows p c (fourColorCycle i)) (hqj : Follows q c (fourColorCycle j))
    (he : p.edges.toFinset = q.edges.toFinset) : i = j := by
  apply fourColorCycle_traversal_index_eq i j (c x)
  have hor := CycleOrientation.cycle_eq_or_reverse hp hq
    (CycleOrientation.edgeSet_eq_of_toFinset_eq he)
  rcases hor with hqeq | hqrev
  · left
    intro r
    have hri := follows_getVert p c (fourColorCycle i) hpi r.val (by omega)
    have hrj := follows_getVert q c (fourColorCycle j) hqj r.val (by rw [hqeq]; omega)
    rw [hqeq] at hrj
    exact hri.symm.trans hrj
  · right
    intro r
    have hri := follows_getVert p c (fourColorCycle i) hpi (4 - r.val) (by omega)
    have hrj := follows_getVert q c (fourColorCycle j) hqj r.val
      (by rw [hqrev, Walk.length_reverse]; omega)
    have hv : q.getVert r.val = p.getVert (4 - r.val) := by
      rw [hqrev, Walk.getVert_reverse, hl]
    exact hri.symm.trans ((congrArg c hv).symm.trans hrj)

end TaskH

#print axioms TaskH.fourColorCycle_traversal_index_eq
#print axioms TaskH.follows_four_cycles_index_eq
