import Research.TaskH.General.RawDescents
import Research.TaskH.General.ClosedColorOrders
import Research.TaskH.GoodMultiplicity

/-!
Actual-walk bridges for the color-order multiplier bound. The first bridge
identifies the dart-filter definition with the word descent count. The
avoid-deleted-vertex case then invokes the closed-word bound on actual colors.
No rainbow, periodicity, or coverage condition is a graph-level hypothesis.
-/

set_option autoImplicit false

universe u

namespace TaskH.General.GoodCycles

open SimpleGraph _root_.TaskH.ColorWords _root_.TaskH.General.ColorWords

variable {k m : ℕ}

variable {V : Type u} {G : SimpleGraph V} {v : V}

/-- The actual dart-filter count equals the descent count of actual vertices. -/
theorem rawDescents_eq_vertexWord {x y : V} (r : V → Fin m) (p : G.Walk x y) :
    rawDescents r p = descents (fun i => r (p.getVert i)) p.length := by
  induction p with
  | nil => simp [rawDescents_nil]
  | @cons x y z h p ih =>
    rw [rawDescents_cons, ih]
    have hs := descents_add (fun i => r ((Walk.cons h p).getVert i)) 1 p.length
    simpa [Walk.length_cons, descents_succ, Nat.add_comm] using hs.symm

/-- The actual deleted-graph colors on every vertex of a walk avoiding v. -/
def avoidingCycleWord {x y : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk x y) (hv : v ∉ p.support) (i : ℕ) : Fin k :=
  c ⟨p.getVert i, by
    intro he
    apply hv
    simpa only [he] using p.getVert_mem_support i⟩

theorem avoidingCycleWord_adj {x y : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk x y) (hv : v ∉ p.support) (i : ℕ) (hi : i < p.length) :
    avoidingCycleWord c p hv i ≠ avoidingCycleWord c p hv (i + 1) := by
  apply c.valid
  exact p.adj_getVert_succ hi

theorem avoidingCycleWord_closed {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk x x) (hv : v ∉ p.support) :
    avoidingCycleWord c p hv p.length = avoidingCycleWord c p hv 0 := by
  unfold avoidingCycleWord
  apply congrArg c
  apply Subtype.ext
  simp

theorem orderColor_avoiding_vertex {x y : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (π : Equiv.Perm (Fin k))
    (p : G.Walk x y) (hv : v ∉ p.support) (i : ℕ) :
    orderColor c π (p.getVert i) = (π (avoidingCycleWord c p hv i)).castSucc := by
  have hxi : p.getVert i ≠ v := by
    intro he
    apply hv
    simpa only [he] using p.getVert_mem_support i
  rw [orderColor_outside c π (p.getVert i) hxi]
  rfl

/-- Exact actual-walk to arbitrary-color-word bridge in the avoid-v case. -/
theorem rawDescents_eq_avoidingWord {x y : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (π : Equiv.Perm (Fin k))
    (p : G.Walk x y) (hv : v ∉ p.support) :
    rawDescents (orderColor c π) p =
      descents (fun i => π (avoidingCycleWord c p hv i)) p.length := by
  rw [rawDescents_eq_vertexWord]
  apply _root_.TaskH.GoodCycles.word_descents_eq_of_steps
  intro i _
  rw [orderColor_avoiding_vertex c π p hv (i + 1), orderColor_avoiding_vertex c π p hv i]
  rfl

/-- At most k orders make a fixed directed closed walk avoiding v good. -/
theorem avoiding_raw_good_orders_card_le (hk : 3 ≤ k) {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk x x) (hv : v ∉ p.support) (a : ℕ) (ha : 1 ≤ a)
    (hlen : p.length = k * a) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
      k * rawDescents (orderColor c π) p ≤ p.length)).card ≤ k := by
  classical
  have heq : (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
        k * rawDescents (orderColor c π) p ≤ p.length)) =
      (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
        descents (fun i => π (avoidingCycleWord c p hv i)) p.length ≤ a)) := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rawDescents_eq_avoidingWord c π p hv]
    constructor
    · intro h
      exact le_of_mul_le_mul_left (h.trans_eq hlen) (by omega : 0 < k)
    · intro h
      exact (Nat.mul_le_mul_left k h).trans_eq hlen.symm
  rw [heq]
  exact closed_low_descent_orders_card_le hk (avoidingCycleWord c p hv) p.length a hlen ha
    (fun i hi => avoidingCycleWord_adj c p hv i hi) (avoidingCycleWord_closed c p hv)

end TaskH.General.GoodCycles

#print axioms TaskH.General.GoodCycles.rawDescents_eq_vertexWord
#print axioms TaskH.General.GoodCycles.avoidingCycleWord
#print axioms TaskH.General.GoodCycles.avoidingCycleWord_adj
#print axioms TaskH.General.GoodCycles.avoidingCycleWord_closed
#print axioms TaskH.General.GoodCycles.orderColor_avoiding_vertex
#print axioms TaskH.General.GoodCycles.rawDescents_eq_avoidingWord
#print axioms TaskH.General.GoodCycles.avoiding_raw_good_orders_card_le
