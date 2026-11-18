import Research.TaskH.General.GoodCycleLowerBound

/-!
Actual original-equality rainbow transport. The lower good-cycle count is
derived from criticality, rather than supplied as R. Each chosen traversal
has a good order: saturation by 2*k and the opposite-direction bound k
exclude an empty direction. The actual color word then gives injectivity.
These are development candidates, not machine-checked declarations.
-/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.General.GoodCycles

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_good_orders_saturated_original (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (s : Finset (Sym2 V)) (hs : s ∈ ModCycleEdgeSets k G) :
    (goodCycleOrders c s).card = 2 * k := by
  exact equality_good_orders_saturated (by omega)
    (GoodCycles.actual_good_cycle_lower_bound hk hcrit) hcount c s hs

theorem equality_deleted_traversal_good_order (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (hlen : p.length = k) :
    ∃ π : Equiv.Perm (Fin k), k * rawDescents (orderColor c π) p ≤ p.length := by
  classical
  have hs : p.edges.toFinset ∈ ModCycleEdgeSets k G :=
    (Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr
      (by simpa only [hlen] using (dvd_refl k))
  have he := equality_good_orders_saturated_original hk hcrit hcount c p.edges.toFinset hs
  have hsub := Finset.card_le_card
    (goodCycleOrders_subset_traversals c p.edges.toFinset p hp p.coe_edges_toFinset.symm)
  have hu := Finset.card_union_le (traversalGoodOrders c p) (traversalGoodOrders c p.reverse)
  have hr : (traversalGoodOrders c p.reverse).card ≤ k :=
    deleted_raw_good_orders_card_le (by omega) c p.reverse hp.reverse 1 (by omega)
      (by simpa only [Walk.length_reverse, Nat.mul_one] using hlen)
  have hpos : 0 < (traversalGoodOrders c p).card := by omega
  obtain ⟨π, hπ⟩ := Finset.card_pos.mp hpos
  exact ⟨π, (mem_traversalGoodOrders c p π).mp hπ⟩

theorem equality_avoiding_traversal_good_order (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v x : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (p : G.Walk x x) (hp : p.IsCycle) (hlen : p.length = k)
    (hv : v ∉ p.support) :
    ∃ π : Equiv.Perm (Fin k), k * rawDescents (orderColor c π) p ≤ p.length := by
  classical
  have hs : p.edges.toFinset ∈ ModCycleEdgeSets k G :=
    (Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr
      (by simpa only [hlen] using (dvd_refl k))
  have he := equality_good_orders_saturated_original hk hcrit hcount c p.edges.toFinset hs
  have hsub := Finset.card_le_card
    (goodCycleOrders_subset_traversals c p.edges.toFinset p hp p.coe_edges_toFinset.symm)
  have hu := Finset.card_union_le (traversalGoodOrders c p) (traversalGoodOrders c p.reverse)
  have hvr : v ∉ p.reverse.support := by
    simpa only [Walk.support_reverse, List.mem_reverse] using hv
  have hr : (traversalGoodOrders c p.reverse).card ≤ k :=
    avoiding_raw_good_orders_card_le (by omega) c p.reverse hvr 1 (by omega)
      (by simpa only [Walk.length_reverse, Nat.mul_one] using hlen)
  have hpos : 0 < (traversalGoodOrders c p).card := by omega
  obtain ⟨π, hπ⟩ := Finset.card_pos.mp hpos
  exact ⟨π, (mem_traversalGoodOrders c p π).mp hπ⟩

theorem equality_deleted_cycle_word_injective (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (hlen : p.length = k) :
    Function.Injective (fun i : Fin (k - 1) => deletedCycleWord (by omega) c p hp i.val) := by
  obtain ⟨π, hπ⟩ := equality_deleted_traversal_good_order hk hcrit hcount c p hp hlen
  have hπmem := (raw_good_iff_deleted_order (by omega) c π p hp 1 (by omega)
    (by simpa only [Nat.mul_one] using hlen)).mp hπ
  have hlow : _root_.TaskH.ColorWords.descents
      (fun i => π (deletedCycleWord (by omega) c p hp i)) (p.length - 2) ≤ 0 := by
    exact (Finset.mem_filter.mp hπmem).2
  exact _root_.TaskH.ColorWords.ranked_prefix_injective (by omega)
    (deletedCycleWord (by omega) c p hp) π (p.length - 2) 0
    (by rw [hlen]; omega)
    (fun i hi => deletedCycleWord_adj (by omega) c p hp i (by omega)) hlow

theorem equality_avoiding_cycle_word_injective (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v x : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (p : G.Walk x x) (hp : p.IsCycle) (hlen : p.length = k)
    (hv : v ∉ p.support) :
    Function.Injective (fun i : Fin k => avoidingCycleWord c p hv i.val) := by
  obtain ⟨π, hπ⟩ := equality_avoiding_traversal_good_order hk hcrit hcount c p hp hlen hv
  rw [rawDescents_eq_avoidingWord c π p hv] at hπ
  have hlow : _root_.TaskH.ColorWords.descents
      (fun i => π (avoidingCycleWord c p hv i)) p.length ≤ 1 := by
    have hmul : k * _root_.TaskH.ColorWords.descents
        (fun i => π (avoidingCycleWord c p hv i)) p.length ≤ k * 1 := by
      simpa only [Nat.mul_one, hlen] using hπ
    exact le_of_mul_le_mul_left hmul (by omega : 0 < k)
  have hsurj := ColorWords.closed_prefix_surjective (by omega)
    (fun i => π (avoidingCycleWord c p hv i)) p.length 1
    (by simpa only [Nat.mul_one] using hlen) (by omega)
    (fun i hi => π.injective.ne (avoidingCycleWord_adj c p hv i hi))
    (congrArg π (avoidingCycleWord_closed c p hv)) hlow
  have hinj : Function.Injective (fun i : Fin k => π (avoidingCycleWord c p hv i.val)) :=
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, rfl⟩).1
  intro i j hij
  exact hinj (congrArg π hij)

theorem equality_deleted_cycle_support_rainbow (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (p : G.Walk v v) (hp : p.IsCycle) (hlen : p.length = k)
    {a b : V} (ha : a ∈ p.support) (hb : b ∈ p.support)
    (hav : a ≠ v) (hbv : b ≠ v) (hc : c ⟨a, hav⟩ = c ⟨b, hbv⟩) : a = b := by
  obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp ha
  obtain ⟨j, hj, hjl⟩ := Walk.mem_support_iff_exists_getVert.mp hb
  have hi0 : 0 < i := by
    by_contra hn
    have hz : i = 0 := by omega
    exact hav (by simpa only [hz, Walk.getVert_zero] using hi.symm)
  have hj0 : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    exact hbv (by simpa only [hz, Walk.getVert_zero] using hj.symm)
  have hik : i < p.length := by
    by_contra hn
    have hz : i = p.length := by omega
    exact hav (by simpa only [hz, Walk.getVert_length] using hi.symm)
  have hjk : j < p.length := by
    by_contra hn
    have hz : j = p.length := by omega
    exact hbv (by simpa only [hz, Walk.getVert_length] using hj.symm)
  let ii : Fin (k - 1) := ⟨i - 1, by omega⟩
  let jj : Fin (k - 1) := ⟨j - 1, by omega⟩
  have hwi : deletedCycleWord (by omega) c p hp ii.val = c ⟨a, hav⟩ := by
    unfold deletedCycleWord
    rw [dite_eq_left (by dsimp [ii]; omega)]
    apply congrArg c
    apply Subtype.ext
    simpa only [ii, Nat.sub_add_cancel (by omega : 1 ≤ i)] using hi
  have hwj : deletedCycleWord (by omega) c p hp jj.val = c ⟨b, hbv⟩ := by
    unfold deletedCycleWord
    rw [dite_eq_left (by dsimp [jj]; omega)]
    apply congrArg c
    apply Subtype.ext
    simpa only [jj, Nat.sub_add_cancel (by omega : 1 ≤ j)] using hj
  have he := equality_deleted_cycle_word_injective hk hcrit hcount c p hp hlen
    (hwi.trans (hc.trans hwj.symm))
  have hvv := congrArg Fin.val he
  have hij : i = j := by dsimp [ii, jj] at hvv; omega
  apply hi.symm.trans
  rw [hij]
  exact hj

theorem equality_avoiding_cycle_support_rainbow (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v x : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (p : G.Walk x x) (hp : p.IsCycle) (hlen : p.length = k)
    (hv : v ∉ p.support) {a b : V} (ha : a ∈ p.support) (hb : b ∈ p.support)
    (hav : a ≠ v) (hbv : b ≠ v) (hc : c ⟨a, hav⟩ = c ⟨b, hbv⟩) : a = b := by
  have hrep : ∀ z ∈ p.support, ∃ i : Fin k, p.getVert i.val = z := by
    intro z hz
    obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hz
    by_cases hik : i < k
    · exact ⟨⟨i, hik⟩, hi⟩
    · have hei : i = p.length := by omega
      refine ⟨⟨0, by omega⟩, ?_⟩
      simpa only [Walk.getVert_zero, hei, Walk.getVert_length] using hi
  obtain ⟨i, hi⟩ := hrep a ha
  obtain ⟨j, hj⟩ := hrep b hb
  have hwi : avoidingCycleWord c p hv i.val = c ⟨a, hav⟩ := by
    unfold avoidingCycleWord
    apply congrArg c
    exact Subtype.ext hi
  have hwj : avoidingCycleWord c p hv j.val = c ⟨b, hbv⟩ := by
    unfold avoidingCycleWord
    apply congrArg c
    exact Subtype.ext hj
  have he := equality_avoiding_cycle_word_injective hk hcrit hcount c p hp hlen hv
    (hwi.trans (hc.trans hwj.symm))
  exact hi.symm.trans ((congrArg (fun t : Fin k => p.getVert t.val) he).trans hj)

/-- R for every actual cycle and every coloring of the whole deleted graph.
The cycle may contain the deleted root or avoid it; no selected cycle or
coloring is supplied as a new Main assumption. -/
theorem equality_original_cycle_support_rainbow (hk : 4 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    {v x : V} (c : (G.induce {z | z ≠ v}).Coloring (Fin k))
    (p : G.Walk x x) (hp : p.IsCycle) (hlen : p.length = k)
    {a b : V} (ha : a ∈ p.support) (hb : b ∈ p.support)
    (hav : a ≠ v) (hbv : b ≠ v) (hc : c ⟨a, hav⟩ = c ⟨b, hbv⟩) : a = b := by
  classical
  by_cases hv : v ∈ p.support
  · let q := p.rotate v hv
    have hq : q.IsCycle := (Walk.isCycle_rotate hv).mpr hp
    have hql : q.length = k := by simpa only [q, Walk.length_rotate] using hlen
    have haq : a ∈ q.support := (Walk.mem_support_rotate_iff p v hv).mpr ha
    have hbq : b ∈ q.support := (Walk.mem_support_rotate_iff p v hv).mpr hb
    exact equality_deleted_cycle_support_rainbow hk hcrit hcount c q hq hql haq hbq hav hbv hc
  · exact equality_avoiding_cycle_support_rainbow hk hcrit hcount c p hp hlen hv ha hb hav hbv hc

end TaskH.General

#print axioms TaskH.General.equality_good_orders_saturated_original
#print axioms TaskH.General.equality_deleted_traversal_good_order
#print axioms TaskH.General.equality_avoiding_traversal_good_order
#print axioms TaskH.General.equality_deleted_cycle_word_injective
#print axioms TaskH.General.equality_avoiding_cycle_word_injective
#print axioms TaskH.General.equality_deleted_cycle_support_rainbow
#print axioms TaskH.General.equality_avoiding_cycle_support_rainbow
#print axioms TaskH.General.equality_original_cycle_support_rainbow
