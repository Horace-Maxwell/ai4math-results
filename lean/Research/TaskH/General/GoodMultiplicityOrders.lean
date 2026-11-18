import Research.TaskH.General.GoodMultiplicityDeleted
import Research.TaskH.GoodMultiplicityOrders

/-!
The actual unoriented-cycle multiplier bound. Arbitrary good witnesses of a
fixed edge set are transported to the two traversals of one genuine cycle by
the already proved cycle-orientation theorem. The word bounds apply to these
actual traversals, with no extra rainbow or coverage premise.
-/

set_option autoImplicit false

universe u

namespace TaskH.General.GoodCycles

open SimpleGraph

variable {k : ℕ}

variable {V : Type u} {G : SimpleGraph V} {v : V}

noncomputable def traversalGoodOrders {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (p : G.Walk x x) :
    Finset (Equiv.Perm (Fin k)) := by
  classical
  exact Finset.univ.filter fun π => k * rawDescents (orderColor c π) p ≤ p.length

noncomputable def goodCycleOrders
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (s : Finset (Sym2 V)) :
    Finset (Equiv.Perm (Fin k)) := by
  classical
  exact Finset.univ.filter fun π => GoodCycleOrder c π s

theorem mem_traversalGoodOrders {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (p : G.Walk x x)
    (π : Equiv.Perm (Fin k)) :
    π ∈ traversalGoodOrders c p ↔ k * rawDescents (orderColor c π) p ≤ p.length := by
  classical
  simp only [traversalGoodOrders, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_goodCycleOrders
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (s : Finset (Sym2 V))
    (π : Equiv.Perm (Fin k)) : π ∈ goodCycleOrders c s ↔ GoodCycleOrder c π s := by
  classical
  simp only [goodCycleOrders, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Any good representative of this edge set has the same divisible length. -/
theorem goodCycleOrder_length_dvd {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (s : Finset (Sym2 V))
    (p : G.Walk x x) (hp : p.IsCycle) (hset : p.edgeSet = (s : Set (Sym2 V)))
    (π : Equiv.Perm (Fin k)) (hgood : GoodCycleOrder c π s) : k ∣ p.length := by
  exact ((goodCycleOrder_iff_traversals c π s p hp hset).mp hgood).1

theorem goodCycleOrders_subset_traversals {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (s : Finset (Sym2 V))
    (p : G.Walk x x) (hp : p.IsCycle) (hset : p.edgeSet = (s : Set (Sym2 V))) :
    goodCycleOrders c s ⊆ traversalGoodOrders c p ∪ traversalGoodOrders c p.reverse := by
  classical
  intro π hπ
  have hgood := ((goodCycleOrder_iff_traversals c π s p hp hset).mp
    ((mem_goodCycleOrders c s π).mp hπ)).2
  rcases hgood with hgood | hgood
  · exact Finset.mem_union_left _ ((mem_traversalGoodOrders c p π).mpr hgood)
  · exact Finset.mem_union_right _ ((mem_traversalGoodOrders c p.reverse π).mpr hgood)

theorem goodCycleOrders_card_le_two_mul_of_cycle (hk : 3 ≤ k) {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (s : Finset (Sym2 V))
    (p : G.Walk x x) (hp : p.IsCycle) (hset : p.edgeSet = (s : Set (Sym2 V)))
    (a : ℕ) (ha : 1 ≤ a) (hlen : p.length = k * a) :
    (goodCycleOrders c s).card ≤ 2 * k := by
  classical
  by_cases hv : v ∈ p.support
  · let q := p.rotate v hv
    have hq : q.IsCycle := (Walk.isCycle_rotate hv).mpr hp
    have hqset : q.edgeSet = (s : Set (Sym2 V)) := (_root_.TaskH.GoodCycles.cycle_rotate_edgeSet_eq p hv).trans hset
    have hqlen : q.length = k * a := by simpa only [q, Walk.length_rotate] using hlen
    have h1 : (traversalGoodOrders c q).card ≤ k :=
      deleted_raw_good_orders_card_le hk c q hq a ha hqlen
    have h2 : (traversalGoodOrders c q.reverse).card ≤ k :=
      deleted_raw_good_orders_card_le hk c q.reverse hq.reverse a ha
        (by simpa only [Walk.length_reverse] using hqlen)
    have hs := Finset.card_le_card (goodCycleOrders_subset_traversals c s q hq hqset)
    have hu := Finset.card_union_le (traversalGoodOrders c q) (traversalGoodOrders c q.reverse)
    omega
  · have hvr : v ∉ p.reverse.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hv
    have h1 : (traversalGoodOrders c p).card ≤ k :=
      avoiding_raw_good_orders_card_le hk c p hv a ha hlen
    have h2 : (traversalGoodOrders c p.reverse).card ≤ k :=
      avoiding_raw_good_orders_card_le hk c p.reverse hvr a ha
        (by simpa only [Walk.length_reverse] using hlen)
    have hs := Finset.card_le_card (goodCycleOrders_subset_traversals c s p hp hset)
    have hu := Finset.card_union_le (traversalGoodOrders c p) (traversalGoodOrders c p.reverse)
    omega

/-- Actual M, including edge sets that do not represent a divisible cycle. -/
theorem goodCycleOrders_card_le_two_mul (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (s : Finset (Sym2 V)) :
    (goodCycleOrders c s).card ≤ 2 * k := by
  classical
  by_cases hS : (goodCycleOrders c s).Nonempty
  · obtain ⟨π, hπ⟩ := hS
    obtain ⟨x, p, hp, hs, hd, _⟩ := (mem_goodCycleOrders c s π).mp hπ
    obtain ⟨a, hlen⟩ := hd
    have hmin := hp.three_le_length
    have ha : 1 ≤ a := by
      by_contra hn
      have hz : a = 0 := by omega
      rw [hz, Nat.mul_zero] at hlen
      omega
    exact goodCycleOrders_card_le_two_mul_of_cycle hk c s p hp hs a ha hlen
  · have he : goodCycleOrders c s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [he]
    simp

theorem goodCycleOrders_card_lt_two_mul_of_long_divisible_cycle (hk : 3 ≤ k) {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (s : Finset (Sym2 V))
    (p : G.Walk x x) (hp : p.IsCycle) (hset : p.edgeSet = (s : Set (Sym2 V)))
    (a : ℕ) (ha : 2 ≤ a) (hlen : p.length = k * a) (hv : v ∈ p.support) :
    (goodCycleOrders c s).card < 2 * k := by
  classical
  let q := p.rotate v hv
  have hq : q.IsCycle := (Walk.isCycle_rotate hv).mpr hp
  have hqset : q.edgeSet = (s : Set (Sym2 V)) := (_root_.TaskH.GoodCycles.cycle_rotate_edgeSet_eq p hv).trans hset
  have hqlen : q.length = k * a := by simpa only [q, Walk.length_rotate] using hlen
  have h1 : (traversalGoodOrders c q).card < k :=
    deleted_raw_good_orders_card_lt hk c q hq a ha hqlen
  have h2 : (traversalGoodOrders c q.reverse).card < k :=
    deleted_raw_good_orders_card_lt hk c q.reverse hq.reverse a ha
      (by simpa only [Walk.length_reverse] using hqlen)
  have hs := Finset.card_le_card (goodCycleOrders_subset_traversals c s q hq hqset)
  have hu := Finset.card_union_le (traversalGoodOrders c q) (traversalGoodOrders c q.reverse)
  omega

/-- The strict actual multiplier bound needs no divisibility premise: if the
fixed genuine cycle has a different residue, no good witness exists. -/
theorem goodCycleOrders_card_lt_two_mul_of_long_cycle (hk : 3 ≤ k) {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (s : Finset (Sym2 V))
    (p : G.Walk x x) (hp : p.IsCycle) (hset : p.edgeSet = (s : Set (Sym2 V)))
    (hlong : 2 * k ≤ p.length) (hv : v ∈ p.support) : (goodCycleOrders c s).card < 2 * k := by
  classical
  by_cases hd : k ∣ p.length
  · obtain ⟨a, hlen⟩ := hd
    have ha : 2 ≤ a := by
      by_contra hn
      have ha1 : a ≤ 1 := by omega
      have hm := Nat.mul_le_mul_left k ha1
      simp only [Nat.mul_one] at hm
      omega
    exact goodCycleOrders_card_lt_two_mul_of_long_divisible_cycle hk c s p hp hset a ha hlen hv
  · have he : goodCycleOrders c s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro π hπ
      exact hd (goodCycleOrder_length_dvd c s p hp hset π ((mem_goodCycleOrders c s π).mp hπ))
    rw [he]
    simp only [Finset.card_empty]
    omega

end TaskH.General.GoodCycles

#print axioms TaskH.General.GoodCycles.traversalGoodOrders
#print axioms TaskH.General.GoodCycles.goodCycleOrders
#print axioms TaskH.General.GoodCycles.mem_traversalGoodOrders
#print axioms TaskH.General.GoodCycles.mem_goodCycleOrders
#print axioms TaskH.General.GoodCycles.goodCycleOrder_length_dvd
#print axioms TaskH.General.GoodCycles.goodCycleOrders_subset_traversals
#print axioms TaskH.General.GoodCycles.goodCycleOrders_card_le_two_mul_of_cycle
#print axioms TaskH.General.GoodCycles.goodCycleOrders_card_le_two_mul
#print axioms TaskH.General.GoodCycles.goodCycleOrders_card_lt_two_mul_of_long_divisible_cycle
#print axioms TaskH.General.GoodCycles.goodCycleOrders_card_lt_two_mul_of_long_cycle
