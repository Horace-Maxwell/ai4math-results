import Research.TaskH.General.GoodMultiplicity
import Research.TaskH.General.DeletedCycleOrders
import Research.TaskH.GoodMultiplicityDeleted

/-!
Actual dart descents for a genuine cycle based at the deleted vertex: the
first edge is a descent, the last edge is not, and the internal edges are
exactly the deleted-cycle color word. This supplies the raw/word bridge
without any graph-level rainbow hypothesis.
-/

set_option autoImplicit false

universe u

namespace TaskH.General.GoodCycles

open SimpleGraph _root_.TaskH.ColorWords _root_.TaskH.General.ColorWords

variable {k : ℕ}

variable {V : Type u} {G : SimpleGraph V} {v : V}

theorem orderColor_cycle_interior_lt
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (π : Equiv.Perm (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (i : ℕ) (hi0 : 0 < i) (hi : i < p.length) :
    orderColor c π (p.getVert i) < Fin.last k := by
  have hneq : p.getVert i ≠ v := by
    intro he
    have he' := (hp.getVert_endpoint_iff (Nat.le_of_lt hi)).mp he
    omega
  rw [orderColor_outside c π (p.getVert i) hneq]
  change (π (c ⟨p.getVert i, hneq⟩)).val < k
  exact (π (c ⟨p.getVert i, hneq⟩)).isLt

theorem orderColor_deleted_vertex (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (π : Equiv.Perm (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (i : ℕ) (hi : i + 1 < p.length) :
    orderColor c π (p.getVert (i + 1)) = (π (deletedCycleWord hk c p hp i)).castSucc := by
  have hneq : p.getVert (i + 1) ≠ v := by
    intro he
    have he' := (hp.getVert_endpoint_iff (Nat.le_of_lt hi)).mp he
    omega
  unfold deletedCycleWord
  rw [dite_eq_left hi]
  exact orderColor_outside c π (p.getVert (i + 1)) hneq

/-- Exact actual-walk bridge: one forced descent plus the interior word. -/
theorem rawDescents_eq_deletedWord (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (π : Equiv.Perm (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) :
    rawDescents (orderColor c π) p =
      1 + descents (fun i => π (deletedCycleWord hk c p hp i)) (p.length - 2) := by
  have hlen := hp.three_le_length
  rw [rawDescents_eq_vertexWord]
  have hbase : orderColor c π (p.getVert 0) = Fin.last k := by
    simpa only [Walk.getVert_zero] using orderColor_base c π
  have hfirst : orderColor c π (p.getVert 1) < orderColor c π (p.getVert 0) := by
    rw [hbase]
    exact orderColor_cycle_interior_lt c π p hp 1 (by omega) (by omega)
  have hlast : ¬ orderColor c π (p.getVert p.length) <
      orderColor c π (p.getVert (p.length - 1)) := by
    rw [Walk.getVert_length, orderColor_base]
    exact not_lt_of_ge (orderColor_cycle_interior_lt c π p hp (p.length - 1)
      (by omega) (by omega)).le
  have hmid : descents (fun i => orderColor c π (p.getVert (1 + i))) (p.length - 2) =
      descents (fun i => π (deletedCycleWord hk c p hp i)) (p.length - 2) := by
    apply _root_.TaskH.GoodCycles.word_descents_eq_of_steps
    intro i hi
    rw [Nat.add_comm 1 (i + 1), Nat.add_comm 1 i]
    have h1 := orderColor_deleted_vertex hk c π p hp i (by omega)
    have h2 := orderColor_deleted_vertex hk c π p hp (i + 1) (by omega)
    simp only [h1, h2, Fin.castSucc_lt_castSucc_iff]
  have hs := _root_.TaskH.GoodCycles.descents_split_ends (fun i => orderColor c π (p.getVert i)) p.length
    (by omega)
  change descents (fun i => orderColor c π (p.getVert i)) p.length =
    (if orderColor c π (p.getVert 1) < orderColor c π (p.getVert 0) then 1 else 0) +
      descents (fun i => orderColor c π (p.getVert (1 + i))) (p.length - 2) +
      (if orderColor c π (p.getVert p.length) <
        orderColor c π (p.getVert (p.length - 1)) then 1 else 0) at hs
  simpa only [ite_eq_left hfirst, ite_eq_right hlast, hmid, Nat.add_zero] using hs

theorem raw_good_iff_deleted_order (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (π : Equiv.Perm (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 1 ≤ a)
    (hlen : p.length = k * a) :
    k * rawDescents (orderColor c π) p ≤ p.length ↔
      π ∈ deletedCycleGoodOrders hk c p hp a := by
  classical
  rw [rawDescents_eq_deletedWord hk c π p hp]
  unfold deletedCycleGoodOrders
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have hm : 1 + descents (fun i => π (deletedCycleWord hk c p hp i)) (p.length - 2) ≤ a :=
      le_of_mul_le_mul_left (h.trans_eq hlen) (by omega : 0 < k)
    omega
  · intro h
    have hm : 1 + descents (fun i => π (deletedCycleWord hk c p hp i)) (p.length - 2) ≤ a := by omega
    exact (Nat.mul_le_mul_left k hm).trans_eq hlen.symm

theorem deleted_raw_good_orders_eq (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 1 ≤ a)
    (hlen : p.length = k * a) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
      k * rawDescents (orderColor c π) p ≤ p.length)) = deletedCycleGoodOrders hk c p hp a := by
  classical
  ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact raw_good_iff_deleted_order hk c π p hp a ha hlen

theorem deleted_raw_good_orders_card_le (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 1 ≤ a)
    (hlen : p.length = k * a) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
      k * rawDescents (orderColor c π) p ≤ p.length)).card ≤ k := by
  classical
  rw [deleted_raw_good_orders_eq hk c p hp a ha hlen]
  exact deletedCycleGoodOrders_card_le hk c p hp a ha hlen

theorem deleted_raw_good_orders_card_lt (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 2 ≤ a)
    (hlen : p.length = k * a) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
      k * rawDescents (orderColor c π) p ≤ p.length)).card < k := by
  classical
  rw [deleted_raw_good_orders_eq hk c p hp a (by omega) hlen]
  exact deletedCycleGoodOrders_card_lt hk c p hp a ha hlen

/-- The two actual raw-direction filters are exactly the two deleted-word filters. -/
theorem deleted_both_raw_good_orders_eq (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 1 ≤ a)
    (hlen : p.length = k * a) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
        k * rawDescents (orderColor c π) p ≤ p.length)) ∪
      (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
        k * rawDescents (orderColor c π) p.reverse ≤ p.reverse.length))) =
      deletedCycleGoodOrders hk c p hp a ∪
        deletedCycleGoodOrders hk c p.reverse hp.reverse a := by
  rw [deleted_raw_good_orders_eq hk c p hp a ha hlen,
    deleted_raw_good_orders_eq hk c p.reverse hp.reverse a ha
      (by simpa only [Walk.length_reverse] using hlen)]

theorem deleted_both_raw_good_orders_card_le (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 1 ≤ a)
    (hlen : p.length = k * a) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
        k * rawDescents (orderColor c π) p ≤ p.length)) ∪
      (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
        k * rawDescents (orderColor c π) p.reverse ≤ p.reverse.length))).card ≤ 2 * k := by
  rw [deleted_both_raw_good_orders_eq hk c p hp a ha hlen]
  exact deletedCycle_both_orders_card_le hk c p hp a ha hlen

theorem deleted_both_raw_good_orders_card_lt (hk : 3 ≤ k)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 2 ≤ a)
    (hlen : p.length = k * a) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
        k * rawDescents (orderColor c π) p ≤ p.length)) ∪
      (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
        k * rawDescents (orderColor c π) p.reverse ≤ p.reverse.length))).card < 2 * k := by
  rw [deleted_both_raw_good_orders_eq hk c p hp a (by omega) hlen]
  exact long_deletedCycle_both_orders_card_lt hk c p hp a ha hlen

/-- A genuine unoriented edge set has precisely the two actual raw-direction
conditions at a chosen representative; changing its base introduces no fiber. -/
theorem goodCycleOrder_iff_traversals {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) (π : Equiv.Perm (Fin k))
    (s : Finset (Sym2 V)) (p : G.Walk x x) (hp : p.IsCycle)
    (hset : p.edgeSet = (s : Set (Sym2 V))) :
    GoodCycleOrder c π s ↔ k ∣ p.length ∧
      (k * rawDescents (orderColor c π) p ≤ p.length ∨
        k * rawDescents (orderColor c π) p.reverse ≤ p.reverse.length) := by
  classical
  constructor
  · rintro ⟨y, q, hq, hqs, hd, hgood⟩
    obtain ⟨hy, hdir⟩ := _root_.TaskH.CycleOrientation.cycle_eq_rotate_or_reverse
      hp hq (hset.trans hqs.symm)
    rcases hdir with hdir | hdir
    · refine ⟨?_, Or.inl ?_⟩
      · simpa only [hdir, Walk.length_rotate] using hd
      · simpa only [hdir, Walk.length_rotate, rawDescents_rotate] using hgood
    · refine ⟨?_, Or.inr ?_⟩
      · simpa only [hdir, Walk.length_reverse, Walk.length_rotate] using hd
      · simpa only [hdir, Walk.length_reverse, Walk.length_rotate,
          rawDescents_rotate_reverse] using hgood
  · rintro ⟨hd, hgood | hgood⟩
    · exact ⟨x, p, hp, hset, hd, hgood⟩
    · refine ⟨x, p.reverse, hp.reverse, ?_, ?_, hgood⟩
      · simpa only [Walk.edgeSet_reverse] using hset
      · simpa only [Walk.length_reverse] using hd

end TaskH.General.GoodCycles

#print axioms TaskH.General.GoodCycles.orderColor_cycle_interior_lt
#print axioms TaskH.General.GoodCycles.orderColor_deleted_vertex
#print axioms TaskH.General.GoodCycles.rawDescents_eq_deletedWord
#print axioms TaskH.General.GoodCycles.raw_good_iff_deleted_order
#print axioms TaskH.General.GoodCycles.deleted_raw_good_orders_eq
#print axioms TaskH.General.GoodCycles.deleted_raw_good_orders_card_le
#print axioms TaskH.General.GoodCycles.deleted_raw_good_orders_card_lt

#print axioms TaskH.General.GoodCycles.deleted_both_raw_good_orders_eq
#print axioms TaskH.General.GoodCycles.deleted_both_raw_good_orders_card_le
#print axioms TaskH.General.GoodCycles.deleted_both_raw_good_orders_card_lt

#print axioms TaskH.General.GoodCycles.goodCycleOrder_iff_traversals
