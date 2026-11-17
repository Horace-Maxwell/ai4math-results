import Research.TaskH.GoodMultiplicity
import Research.TaskH.DeletedCycleOrders

/-!
Actual dart descents for a genuine cycle based at the deleted vertex: the
first edge is a descent, the last edge is not, and the internal edges are
exactly the deleted-cycle color word. This supplies the raw/word bridge
without any graph-level rainbow hypothesis.
-/

set_option autoImplicit false

universe u

namespace TaskH.GoodCycles

open SimpleGraph ColorWords

variable {V : Type u} {G : SimpleGraph V} {v : V}

theorem descents_split_ends {k : ℕ} (w : ℕ → Fin k) (L : ℕ) (hL : 2 ≤ L) :
    descents w L = (if w 1 < w 0 then 1 else 0) +
      descents (fun i => w (1 + i)) (L - 2) +
      if w L < w (L - 1) then 1 else 0 := by
  have hlen1 : 1 + (L - 1) = L := by omega
  have hlen2 : L - 2 + 1 = L - 1 := by omega
  have hidx0 : 1 + (L - 2) = L - 1 := by omega
  have hidx1 : 1 + (L - 2 + 1) = L := by omega
  have hsplit1 := descents_add w 1 (L - 1)
  rw [hlen1] at hsplit1
  have hsplit2 := descents_add (fun i => w (1 + i)) (L - 2) 1
  rw [hlen2] at hsplit2
  have hfirst : descents w 1 = if w 1 < w 0 then 1 else 0 := by
    simp only [descents_succ, descents_zero, zero_add]
  have hlast : descents (fun i => w (1 + (L - 2 + i))) 1 =
      if w L < w (L - 1) then 1 else 0 := by
    change (0 + (if w (1 + (L - 2 + 1)) < w (1 + (L - 2 + 0))
      then 1 else 0)) = _
    simp only [Nat.add_zero, hidx0, hidx1, zero_add]
  simpa only [hfirst, hsplit2, hlast, Nat.add_assoc] using hsplit1

theorem orderColor_cycle_interior_lt
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (π : Equiv.Perm (Fin 4))
    (p : G.Walk v v) (hp : p.IsCycle) (i : ℕ) (hi0 : 0 < i) (hi : i < p.length) :
    orderColor c π (p.getVert i) < (4 : Fin 5) := by
  have hneq : p.getVert i ≠ v := by
    intro he
    have he' := (hp.getVert_endpoint_iff (Nat.le_of_lt hi)).mp he
    omega
  rw [orderColor_outside c π (p.getVert i) hneq]
  change (π (c ⟨p.getVert i, hneq⟩)).val < 4
  exact (π (c ⟨p.getVert i, hneq⟩)).isLt

theorem orderColor_deleted_vertex
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (π : Equiv.Perm (Fin 4))
    (p : G.Walk v v) (hp : p.IsCycle) (i : ℕ) (hi : i + 1 < p.length) :
    orderColor c π (p.getVert (i + 1)) = (π (deletedCycleWord c p hp i)).castSucc := by
  have hneq : p.getVert (i + 1) ≠ v := by
    intro he
    have he' := (hp.getVert_endpoint_iff (Nat.le_of_lt hi)).mp he
    omega
  unfold deletedCycleWord
  rw [dite_eq_left hi]
  exact orderColor_outside c π (p.getVert (i + 1)) hneq

/-- Exact actual-walk bridge: one forced descent plus the interior word. -/
theorem rawDescents_eq_deletedWord
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (π : Equiv.Perm (Fin 4))
    (p : G.Walk v v) (hp : p.IsCycle) :
    rawDescents (orderColor c π) p =
      1 + descents (fun i => π (deletedCycleWord c p hp i)) (p.length - 2) := by
  have hlen := hp.three_le_length
  rw [rawDescents_eq_vertexWord]
  have hbase : orderColor c π (p.getVert 0) = 4 := by
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
      descents (fun i => π (deletedCycleWord c p hp i)) (p.length - 2) := by
    apply word_descents_eq_of_steps
    intro i hi
    rw [Nat.add_comm 1 (i + 1), Nat.add_comm 1 i]
    have h1 := orderColor_deleted_vertex c π p hp i (by omega)
    have h2 := orderColor_deleted_vertex c π p hp (i + 1) (by omega)
    simp only [h1, h2, Fin.castSucc_lt_castSucc_iff]
  have hs := descents_split_ends (fun i => orderColor c π (p.getVert i)) p.length
    (by omega)
  change descents (fun i => orderColor c π (p.getVert i)) p.length =
    (if orderColor c π (p.getVert 1) < orderColor c π (p.getVert 0) then 1 else 0) +
      descents (fun i => orderColor c π (p.getVert (1 + i))) (p.length - 2) +
      (if orderColor c π (p.getVert p.length) <
        orderColor c π (p.getVert (p.length - 1)) then 1 else 0) at hs
  simpa only [ite_eq_left hfirst, ite_eq_right hlast, hmid, Nat.add_zero] using hs

theorem raw_good_iff_deleted_order
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (π : Equiv.Perm (Fin 4))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 1 ≤ a)
    (hlen : p.length = 4 * a) :
    4 * rawDescents (orderColor c π) p ≤ p.length ↔
      π ∈ deletedCycleGoodOrders c p hp a := by
  classical
  rw [rawDescents_eq_deletedWord c π p hp]
  unfold deletedCycleGoodOrders
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem deleted_raw_good_orders_eq
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 1 ≤ a)
    (hlen : p.length = 4 * a) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 4) =>
      4 * rawDescents (orderColor c π) p ≤ p.length)) = deletedCycleGoodOrders c p hp a := by
  classical
  ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact raw_good_iff_deleted_order c π p hp a ha hlen

theorem deleted_raw_good_orders_card_le_four
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 1 ≤ a)
    (hlen : p.length = 4 * a) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 4) =>
      4 * rawDescents (orderColor c π) p ≤ p.length)).card ≤ 4 := by
  classical
  rw [deleted_raw_good_orders_eq c p hp a ha hlen]
  exact deletedCycleGoodOrders_card_le_four c p hp a ha hlen

theorem deleted_raw_good_orders_card_lt_four
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4))
    (p : G.Walk v v) (hp : p.IsCycle) (a : ℕ) (ha : 2 ≤ a)
    (hlen : p.length = 4 * a) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin 4) =>
      4 * rawDescents (orderColor c π) p ≤ p.length)).card < 4 := by
  classical
  rw [deleted_raw_good_orders_eq c p hp a (by omega) hlen]
  exact deletedCycleGoodOrders_card_lt_four c p hp a ha hlen

end TaskH.GoodCycles

#print axioms TaskH.GoodCycles.descents_split_ends
#print axioms TaskH.GoodCycles.rawDescents_eq_deletedWord
#print axioms TaskH.GoodCycles.deleted_raw_good_orders_eq
#print axioms TaskH.GoodCycles.deleted_raw_good_orders_card_lt_four
