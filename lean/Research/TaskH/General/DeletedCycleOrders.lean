import Research.TaskH.General.ColorWordsSaturation
import Research.TaskH.Critical

set_option autoImplicit false

universe u

namespace TaskH.General

variable {k : ℕ}

open SimpleGraph _root_.TaskH.ColorWords _root_.TaskH.General.ColorWords

variable {V : Type u} {G : SimpleGraph V} {v : V}

/-- The actual colors of a cycle after deleting its base vertex. Values past
the finite interior segment are padded with zero and are never counted. -/
def deletedCycleWord (hk : 3 ≤ k) (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (i : ℕ) : Fin k :=
  if hi : i + 1 < p.length then
    c ⟨p.getVert (i + 1), by
      intro he
      have hends := (hp.getVert_endpoint_iff (Nat.le_of_lt hi)).mp he
      omega⟩
  else ⟨0, by omega⟩

theorem deletedCycleWord_adj (hk : 3 ≤ k) (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (i : ℕ) (hi : i + 2 < p.length) :
    deletedCycleWord hk c p hp i ≠ deletedCycleWord hk c p hp (i + 1) := by
  have h1 : i + 1 < p.length := by omega
  have h2 : i + 1 + 1 < p.length := by omega
  unfold deletedCycleWord
  rw [dite_eq_left h1, dite_eq_left h2]
  apply c.valid
  exact p.adj_getVert_succ (by omega)

/-- Orders good for this directed traversal in the over-deleted-vertex part
of the multiplicity argument. The departure from v contributes one forced descent. -/
noncomputable def deletedCycleGoodOrders (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) : Finset (Equiv.Perm (Fin k)) := by
  classical
  exact Finset.univ.filter fun π =>
    descents (fun i => π (deletedCycleWord hk c p hp i)) (p.length - 2) ≤ a - 1

theorem deletedCycleGoodOrders_card_le (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 1 ≤ a)
    (hlen : p.length = k * a) : (deletedCycleGoodOrders hk c p hp a).card ≤ k := by
  classical
  apply low_descent_orders_card_le hk (deletedCycleWord hk c p hp)
    (p.length - 2) (a - 1)
  · have htwo : 2 ≤ p.length := by have := hp.three_le_length; omega
    rw [Nat.sub_add_cancel htwo, Nat.sub_add_cancel ha]
    exact hlen
  · intro i hi
    exact deletedCycleWord_adj hk c p hp i (by omega)

theorem deletedCycleGoodOrders_card_lt (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 2 ≤ a)
    (hlen : p.length = k * a) : (deletedCycleGoodOrders hk c p hp a).card < k := by
  classical
  apply low_descent_orders_card_lt hk (deletedCycleWord hk c p hp) (p.length - 2) (a - 1)
  · have htwo : 2 ≤ p.length := by have := hp.three_le_length; omega
    rw [Nat.sub_add_cancel htwo, Nat.sub_add_cancel (show 1 ≤ a by omega)]
    exact hlen
  · omega
  · intro i hi
    exact deletedCycleWord_adj hk c p hp i (by omega)

theorem deletedCycle_both_orders_card_le (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 1 ≤ a)
    (hlen : p.length = k * a) :
    (deletedCycleGoodOrders hk c p hp a ∪
      deletedCycleGoodOrders hk c p.reverse hp.reverse a).card ≤ 2 * k := by
  classical
  have h1 := deletedCycleGoodOrders_card_le hk c p hp a ha hlen
  have h2 := deletedCycleGoodOrders_card_le hk c p.reverse hp.reverse a ha
    (by simpa only [Walk.length_reverse] using hlen)
  have hu := Finset.card_union_le (deletedCycleGoodOrders hk c p hp a)
    (deletedCycleGoodOrders hk c p.reverse hp.reverse a)
  omega

theorem long_deletedCycle_both_orders_card_lt (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 2 ≤ a)
    (hlen : p.length = k * a) :
    (deletedCycleGoodOrders hk c p hp a ∪
      deletedCycleGoodOrders hk c p.reverse hp.reverse a).card < 2 * k := by
  classical
  have h1 := deletedCycleGoodOrders_card_lt hk c p hp a ha hlen
  have h2 := deletedCycleGoodOrders_card_lt hk c p.reverse hp.reverse a ha
    (by simpa only [Walk.length_reverse] using hlen)
  have hu := Finset.card_union_le (deletedCycleGoodOrders hk c p hp a)
    (deletedCycleGoodOrders hk c p.reverse hp.reverse a)
  omega

/-- One coloring is obtained internally from the original proper-subgraph
criticality hypothesis and works for every actual cycle based at v. -/
theorem critical_deletedCycle_orders (hk : 3 ≤ k)
    (hcrit : _root_.TaskH.Challenge.IsCriticalPlus k G) (v : V) :
    ∃ c : (G.induce {x | x ≠ v}).Coloring (Fin k),
      ∀ (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ), p.length = k * a →
        (1 ≤ a → (deletedCycleGoodOrders hk c p hp a ∪
          deletedCycleGoodOrders hk c p.reverse hp.reverse a).card ≤ 2 * k) ∧
        (2 ≤ a → (deletedCycleGoodOrders hk c p hp a ∪
          deletedCycleGoodOrders hk c p.reverse hp.reverse a).card < 2 * k) := by
  obtain ⟨c⟩ := _root_.TaskH.critical_colorable_deletedVertex hcrit v
  refine ⟨c, ?_⟩
  intro p hp a hlen
  exact ⟨fun ha => deletedCycle_both_orders_card_le hk c p hp a ha hlen,
    fun ha => long_deletedCycle_both_orders_card_lt hk c p hp a ha hlen⟩

#print axioms deletedCycleWord
#print axioms deletedCycleWord_adj
#print axioms deletedCycleGoodOrders
#print axioms deletedCycleGoodOrders_card_le
#print axioms deletedCycleGoodOrders_card_lt
#print axioms deletedCycle_both_orders_card_le
#print axioms long_deletedCycle_both_orders_card_lt
#print axioms critical_deletedCycle_orders

end TaskH.General
