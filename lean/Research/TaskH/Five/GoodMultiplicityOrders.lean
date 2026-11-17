import Research.TaskH.Five.GoodMultiplicityDeleted

/-!
The actual unoriented-cycle multiplier bound. Arbitrary good witnesses of a
fixed edge set are transported to the two traversals of one genuine cycle by
the already proved cycle-orientation theorem. The word bounds apply to these
actual traversals, with no extra rainbow or coverage premise.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five.GoodCycles

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {v : V}

noncomputable def traversalGoodOrders {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (p : G.Walk x x) :
    Finset (Equiv.Perm (Fin 5)) := by
  classical
  exact Finset.univ.filter fun π => 5 * rawDescents (orderColor c π) p ≤ p.length

noncomputable def goodCycleOrders
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (s : Finset (Sym2 V)) :
    Finset (Equiv.Perm (Fin 5)) := by
  classical
  exact Finset.univ.filter fun π => GoodCycleOrder c π s

theorem mem_traversalGoodOrders {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (p : G.Walk x x)
    (π : Equiv.Perm (Fin 5)) :
    π ∈ traversalGoodOrders c p ↔ 5 * rawDescents (orderColor c π) p ≤ p.length := by
  classical
  simp only [traversalGoodOrders, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_goodCycleOrders
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (s : Finset (Sym2 V))
    (π : Equiv.Perm (Fin 5)) : π ∈ goodCycleOrders c s ↔ GoodCycleOrder c π s := by
  classical
  simp only [goodCycleOrders, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Any good representative of this edge set has the same divisible length. -/
theorem goodCycleOrder_length_dvd {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (s : Finset (Sym2 V))
    (p : G.Walk x x) (hp : p.IsCycle) (hset : p.edgeSet = (s : Set (Sym2 V)))
    (π : Equiv.Perm (Fin 5)) (hgood : GoodCycleOrder c π s) : 5 ∣ p.length := by
  classical
  obtain ⟨y, q, hq, hqs, hd, _⟩ := hgood
  obtain ⟨hy, hdir⟩ := CycleOrientation.cycle_eq_rotate_or_reverse hp hq (hset.trans hqs.symm)
  rcases hdir with hdir | hdir
  · simpa only [hdir, Walk.length_rotate] using hd
  · simpa only [hdir, Walk.length_reverse, Walk.length_rotate] using hd

theorem goodCycleOrders_subset_traversals {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (s : Finset (Sym2 V))
    (p : G.Walk x x) (hp : p.IsCycle) (hset : p.edgeSet = (s : Set (Sym2 V))) :
    goodCycleOrders c s ⊆ traversalGoodOrders c p ∪ traversalGoodOrders c p.reverse := by
  classical
  intro π hπ
  obtain ⟨y, q, hq, hqs, _, hgood⟩ := (mem_goodCycleOrders c s π).mp hπ
  obtain ⟨hy, hdir⟩ := CycleOrientation.cycle_eq_rotate_or_reverse hp hq (hset.trans hqs.symm)
  apply Finset.mem_union.mpr
  rcases hdir with hdir | hdir
  · left
    apply (mem_traversalGoodOrders c p π).mpr
    simpa only [hdir, Walk.length_rotate, rawDescents_rotate] using hgood
  · right
    apply (mem_traversalGoodOrders c p.reverse π).mpr
    simpa only [hdir, Walk.length_reverse, Walk.length_rotate, rawDescents_rotate_reverse]
      using hgood

theorem cycle_rotate_edgeSet_eq [DecidableEq V] {x : V} (p : G.Walk x x)
    (hv : v ∈ p.support) :
    (p.rotate v hv).edgeSet = p.edgeSet := by
  ext e
  change e ∈ (p.rotate v hv).edges ↔ e ∈ p.edges
  exact (p.rotate_edges v hv).perm.mem_iff

theorem goodCycleOrders_card_le_ten_of_cycle {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (s : Finset (Sym2 V))
    (p : G.Walk x x) (hp : p.IsCycle) (hset : p.edgeSet = (s : Set (Sym2 V)))
    (a : ℕ) (ha : 1 ≤ a) (hlen : p.length = 5 * a) :
    (goodCycleOrders c s).card ≤ 10 := by
  classical
  by_cases hv : v ∈ p.support
  · let q := p.rotate v hv
    have hq : q.IsCycle := (Walk.isCycle_rotate hv).mpr hp
    have hqset : q.edgeSet = (s : Set (Sym2 V)) := (cycle_rotate_edgeSet_eq p hv).trans hset
    have hqlen : q.length = 5 * a := by simpa only [q, Walk.length_rotate] using hlen
    have h1 : (traversalGoodOrders c q).card ≤ 5 :=
      deleted_raw_good_orders_card_le_five c q hq a ha hqlen
    have h2 : (traversalGoodOrders c q.reverse).card ≤ 5 :=
      deleted_raw_good_orders_card_le_five c q.reverse hq.reverse a ha
        (by simpa only [Walk.length_reverse] using hqlen)
    have hs := Finset.card_le_card (goodCycleOrders_subset_traversals c s q hq hqset)
    have hu := Finset.card_union_le (traversalGoodOrders c q) (traversalGoodOrders c q.reverse)
    omega
  · have hvr : v ∉ p.reverse.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hv
    have h1 : (traversalGoodOrders c p).card ≤ 5 :=
      avoiding_raw_good_orders_card_le_five c p hv a ha hlen
    have h2 : (traversalGoodOrders c p.reverse).card ≤ 5 :=
      avoiding_raw_good_orders_card_le_five c p.reverse hvr a ha
        (by simpa only [Walk.length_reverse] using hlen)
    have hs := Finset.card_le_card (goodCycleOrders_subset_traversals c s p hp hset)
    have hu := Finset.card_union_le (traversalGoodOrders c p) (traversalGoodOrders c p.reverse)
    omega

/-- Actual M, including edge sets that do not represent a divisible cycle. -/
theorem goodCycleOrders_card_le_ten
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (s : Finset (Sym2 V)) :
    (goodCycleOrders c s).card ≤ 10 := by
  classical
  by_cases hS : (goodCycleOrders c s).Nonempty
  · obtain ⟨π, hπ⟩ := hS
    obtain ⟨x, p, hp, hs, hd, _⟩ := (mem_goodCycleOrders c s π).mp hπ
    obtain ⟨a, hlen⟩ := hd
    have hmin := hp.three_le_length
    have ha : 1 ≤ a := by omega
    exact goodCycleOrders_card_le_ten_of_cycle c s p hp hs a ha hlen
  · have he : goodCycleOrders c s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [he]
    simp

theorem goodCycleOrders_card_lt_ten_of_long_divisible_cycle {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (s : Finset (Sym2 V))
    (p : G.Walk x x) (hp : p.IsCycle) (hset : p.edgeSet = (s : Set (Sym2 V)))
    (a : ℕ) (ha : 2 ≤ a) (hlen : p.length = 5 * a) (hv : v ∈ p.support) :
    (goodCycleOrders c s).card < 10 := by
  classical
  let q := p.rotate v hv
  have hq : q.IsCycle := (Walk.isCycle_rotate hv).mpr hp
  have hqset : q.edgeSet = (s : Set (Sym2 V)) := (cycle_rotate_edgeSet_eq p hv).trans hset
  have hqlen : q.length = 5 * a := by simpa only [q, Walk.length_rotate] using hlen
  have h1 : (traversalGoodOrders c q).card < 5 :=
    deleted_raw_good_orders_card_lt_five c q hq a ha hqlen
  have h2 : (traversalGoodOrders c q.reverse).card < 5 :=
    deleted_raw_good_orders_card_lt_five c q.reverse hq.reverse a ha
      (by simpa only [Walk.length_reverse] using hqlen)
  have hs := Finset.card_le_card (goodCycleOrders_subset_traversals c s q hq hqset)
  have hu := Finset.card_union_le (traversalGoodOrders c q) (traversalGoodOrders c q.reverse)
  omega

/-- The strict actual multiplier bound needs no divisibility premise: if the
fixed genuine cycle has a different residue, no good witness exists. -/
theorem goodCycleOrders_card_lt_ten_of_long_cycle {x : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) (s : Finset (Sym2 V))
    (p : G.Walk x x) (hp : p.IsCycle) (hset : p.edgeSet = (s : Set (Sym2 V)))
    (hlong : 10 ≤ p.length) (hv : v ∈ p.support) : (goodCycleOrders c s).card < 10 := by
  classical
  by_cases hd : 5 ∣ p.length
  · obtain ⟨a, hlen⟩ := hd
    have ha : 2 ≤ a := by omega
    exact goodCycleOrders_card_lt_ten_of_long_divisible_cycle c s p hp hset a ha hlen hv
  · have he : goodCycleOrders c s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro π hπ
      exact hd (goodCycleOrder_length_dvd c s p hp hset π ((mem_goodCycleOrders c s π).mp hπ))
    rw [he]
    simp

end TaskH.Five.GoodCycles

#print axioms TaskH.Five.GoodCycles.traversalGoodOrders
#print axioms TaskH.Five.GoodCycles.goodCycleOrders
#print axioms TaskH.Five.GoodCycles.mem_traversalGoodOrders
#print axioms TaskH.Five.GoodCycles.mem_goodCycleOrders
#print axioms TaskH.Five.GoodCycles.goodCycleOrder_length_dvd
#print axioms TaskH.Five.GoodCycles.goodCycleOrders_subset_traversals
#print axioms TaskH.Five.GoodCycles.cycle_rotate_edgeSet_eq
#print axioms TaskH.Five.GoodCycles.goodCycleOrders_card_le_ten_of_cycle
#print axioms TaskH.Five.GoodCycles.goodCycleOrders_card_le_ten
#print axioms TaskH.Five.GoodCycles.goodCycleOrders_card_lt_ten_of_long_divisible_cycle
#print axioms TaskH.Five.GoodCycles.goodCycleOrders_card_lt_ten_of_long_cycle
