import Research.TaskH.Six.ColorWordsSaturation
import Research.TaskH.Critical

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.ColorWords _root_.TaskH.Six.ColorWords

variable {V : Type u} {G : SimpleGraph V} {v : V}

/-- The actual colors of a cycle after deleting its base vertex. Values past
the finite interior segment are padded with zero and are never counted. -/
def deletedCycleWord (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (p : G.Walk v v) (hp : p.IsCycle) (i : ℕ) : Fin 6 :=
  if hi : i + 1 < p.length then
    c ⟨p.getVert (i + 1), by
      intro he
      have hends := (hp.getVert_endpoint_iff (Nat.le_of_lt hi)).mp he
      omega⟩
  else 0

theorem deletedCycleWord_adj (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (p : G.Walk v v) (hp : p.IsCycle) (i : ℕ) (hi : i + 2 < p.length) :
    deletedCycleWord c p hp i ≠ deletedCycleWord c p hp (i + 1) := by
  have h1 : i + 1 < p.length := by omega
  have h2 : i + 1 + 1 < p.length := by omega
  unfold deletedCycleWord
  rw [dite_eq_left h1, dite_eq_left h2]
  apply c.valid
  exact p.adj_getVert_succ (by omega)

/-- Orders good for this directed traversal in the over-deleted-vertex part
of the multiplicity argument. The final return through v is one descent. -/
noncomputable def deletedCycleGoodOrders
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) : Finset (Equiv.Perm (Fin 6)) := by
  classical
  exact Finset.univ.filter fun π =>
    descents (fun i => π (deletedCycleWord c p hp i)) (p.length - 2) ≤ a - 1

theorem deletedCycleGoodOrders_card_le_six
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 1 ≤ a)
    (hlen : p.length = 6 * a) : (deletedCycleGoodOrders c p hp a).card ≤ 6 := by
  classical
  apply low_descent_orders_card_le (by decide) (deletedCycleWord c p hp)
    (p.length - 2) (a - 1)
  · omega
  · intro i hi
    exact deletedCycleWord_adj c p hp i (by omega)

theorem deletedCycleGoodOrders_card_lt_six
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 2 ≤ a)
    (hlen : p.length = 6 * a) : (deletedCycleGoodOrders c p hp a).card < 6 := by
  classical
  apply low_descent_orders_card_lt6 (deletedCycleWord c p hp) (p.length - 2) (a - 1)
  · omega
  · omega
  · intro i hi
    exact deletedCycleWord_adj c p hp i (by omega)

theorem deletedCycle_both_orders_card_le_twelve
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 1 ≤ a)
    (hlen : p.length = 6 * a) :
    (deletedCycleGoodOrders c p hp a ∪
      deletedCycleGoodOrders c p.reverse hp.reverse a).card ≤ 12 := by
  classical
  have h1 := deletedCycleGoodOrders_card_le_six c p hp a ha hlen
  have h2 := deletedCycleGoodOrders_card_le_six c p.reverse hp.reverse a ha
    (by simpa only [Walk.length_reverse] using hlen)
  have hu := Finset.card_union_le (deletedCycleGoodOrders c p hp a)
    (deletedCycleGoodOrders c p.reverse hp.reverse a)
  omega

theorem long_deletedCycle_both_orders_card_lt_twelve
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 2 ≤ a)
    (hlen : p.length = 6 * a) :
    (deletedCycleGoodOrders c p hp a ∪
      deletedCycleGoodOrders c p.reverse hp.reverse a).card < 12 := by
  classical
  have h1 := deletedCycleGoodOrders_card_lt_six c p hp a ha hlen
  have h2 := deletedCycleGoodOrders_card_lt_six c p.reverse hp.reverse a ha
    (by simpa only [Walk.length_reverse] using hlen)
  have hu := Finset.card_union_le (deletedCycleGoodOrders c p hp a)
    (deletedCycleGoodOrders c p.reverse hp.reverse a)
  omega

#print axioms deletedCycleWord
#print axioms deletedCycleWord_adj
#print axioms deletedCycleGoodOrders
#print axioms deletedCycleGoodOrders_card_le_six
#print axioms deletedCycleGoodOrders_card_lt_six
#print axioms deletedCycle_both_orders_card_le_twelve
#print axioms long_deletedCycle_both_orders_card_lt_twelve

end TaskH.Six
