import Research.TaskH.Seven.SingletonNeighborColors
import Research.TaskH.Seven.EdgeCyclesCount

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def singletonEdgeColoring (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i : ↥(singletonNeighborColors v c)) :
    (G.deleteEdges {s(v, (singletonNeighbor v c i).val)}).Coloring (Fin 7) := by
  classical
  refine SimpleGraph.Coloring.mk (fun x => if hx : x = v then i.val else c ⟨x, hx⟩) ?_
  intro a b hab
  have hg := (SimpleGraph.deleteEdges_adj.mp hab).1
  have hn : s(a, b) ≠ s(v, (singletonNeighbor v c i).val) := by
    simpa only [Set.mem_singleton_iff] using (SimpleGraph.deleteEdges_adj.mp hab).2
  by_cases ha : a = v
  · subst a
    have hb : b ≠ v := hg.ne.symm
    simp only [dite_eq_right hb]
    intro he
    have hsel := singletonNeighbor_eq_of_color v c i ⟨b, hg⟩ he.symm
    have hbsel : b = (singletonNeighbor v c i).val := congrArg Subtype.val hsel
    exact hn (by rw [hbsel])
  · by_cases hb : b = v
    · subst b
      simp only [dite_eq_right ha]
      intro he
      have hsel := singletonNeighbor_eq_of_color v c i ⟨a, hg.symm⟩ he
      have hasel : a = (singletonNeighbor v c i).val := congrArg Subtype.val hsel
      exact hn (by rw [hasel]; exact Sym2.eq_swap)
    · simp only [dite_eq_right ha, dite_eq_right hb]
      exact c.valid hg

theorem singletonEdgeColoring_base (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i : ↥(singletonNeighborColors v c)) : singletonEdgeColoring v c i v = i.val := by
  classical
  change (if hx : v = v then i.val else c ⟨v, hx⟩) = i.val
  exact dite_eq_left rfl

theorem singletonEdgeColoring_outside (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i : ↥(singletonNeighborColors v c)) (x : V) (hx : x ≠ v) :
    singletonEdgeColoring v c i x = c ⟨x, hx⟩ := by
  classical
  change (if h : x = v then i.val else c ⟨x, h⟩) = c ⟨x, hx⟩
  exact dite_eq_right hx

/-- Every rank order has a genuine witness for this same singleton coloring. -/
theorem singleton_through_ordered_cycle (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i : ↥(singletonNeighborColors v c)) (π : Equiv.Perm (Fin 7)) :
    ∃ p : G.Walk v v, p.IsCycle ∧ p.length = 7 ∧
      Follows p (fun z => π (singletonEdgeColoring v c i z)) (finRotate 7) ∧
      (singletonNeighbor v c i).val ∉ p.support :=
  critical_edge_ordered_seven_cycle hcrit hs (singletonNeighbor v c i).property
    (singletonEdgeColoring v c i) π

/-- The original deleted-vertex word on such a cycle omits precisely its
singleton color. This assertion applies to any actual following witness. -/
theorem singleton_cycle_missing_color
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i : ↥(singletonNeighborColors v c)) (π : Equiv.Perm (Fin 7))
    (p : G.Walk v v) (hlen : p.length = 7)
    (hf : Follows p (fun z => π (singletonEdgeColoring v c i z)) (finRotate 7))
    (z : {x : V // x ≠ v}) (hz : z.val ∈ p.support) : c z ≠ i.val := by
  intro hc
  have he : π (singletonEdgeColoring v c i z.val) = π (singletonEdgeColoring v c i v) := by
    rw [singletonEdgeColoring_outside v c i z.val z.property, singletonEdgeColoring_base]
    change π (c z) = π i.val
    exact congrArg π hc
  exact follows_seven_cycle_avoids_same_color p _ hf hlen he z.property.symm hz

theorem singleton_cycle_visits_other_color
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i : ↥(singletonNeighborColors v c)) (π : Equiv.Perm (Fin 7))
    (p : G.Walk v v) (hlen : p.length = 7)
    (hf : Follows p (fun z => π (singletonEdgeColoring v c i z)) (finRotate 7))
    (t : Fin 7) (hit : i.val ≠ t) :
    ∃ z : {x : V // x ≠ v}, c z = t ∧ z.val ∈ p.support := by
  obtain ⟨r, hr⟩ := rotate_seven_orbit_surjective (π i.val) (π t)
  have hfollow := follows_getVert p (fun z => π (singletonEdgeColoring v c i z))
    (finRotate 7) hf r.val (by have := r.isLt; omega)
  rw [singletonEdgeColoring_base] at hfollow
  have hzv : p.getVert r.val ≠ v := by
    intro he
    rw [he, singletonEdgeColoring_base] at hfollow
    exact hit (π.injective (hfollow.trans hr))
  let z : {x : V // x ≠ v} := ⟨p.getVert r.val, hzv⟩
  have hzassigned : singletonEdgeColoring v c i z.val = t := π.injective (hfollow.trans hr)
  have hzcolor : c z = t :=
    (singletonEdgeColoring_outside v c i z.val z.property).symm.trans hzassigned
  exact ⟨z, hzcolor, p.getVert_mem_support r.val⟩

/-- A cycle edge set cannot occur for two different omitted colors. -/
theorem singleton_order_color_eq
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i j : ↥(singletonNeighborColors v c)) (π ρ : Equiv.Perm (Fin 7))
    (s : Finset (Sym2 V))
    (hi : π ∈ basedCycleOrders (G := G) (singletonEdgeColoring v c i) v s)
    (hj : ρ ∈ basedCycleOrders (G := G) (singletonEdgeColoring v c j) v s) : i = j := by
  obtain ⟨p, hp, hplen, hps, hpf⟩ := (mem_basedCycleOrders _ v s π).mp hi
  obtain ⟨q, hq, hqlen, hqs, hqf⟩ := (mem_basedCycleOrders _ v s ρ).mp hj
  by_contra hne
  have hvals : j.val ≠ i.val := fun he => hne (Subtype.ext he.symm)
  obtain ⟨z, hzc, hzq⟩ := singleton_cycle_visits_other_color v c j ρ q hqlen hqf i.val hvals
  have hzp : z.val ∈ p.support := by
    obtain hdir | hdir := CycleOrientation.cycle_eq_or_reverse hp hq (hps.trans hqs.symm)
    · simpa only [hdir] using hzq
    · simpa only [hdir, Walk.support_reverse, List.mem_reverse] using hzq
  exact singleton_cycle_missing_color v c i π p hplen hpf z hzp hzc

noncomputable def singletonOrders (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (s : Finset (Sym2 V)) :
    Finset (↥(singletonNeighborColors v c) × Equiv.Perm (Fin 7)) := by
  classical
  exact Finset.univ.filter (fun t => t.2 ∈
    basedCycleOrders (G := G) (singletonEdgeColoring v c t.1) v s)

theorem mem_singletonOrders (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (s : Finset (Sym2 V))
    (t : ↥(singletonNeighborColors v c) × Equiv.Perm (Fin 7)) :
    t ∈ singletonOrders v c s ↔ t.2 ∈
      basedCycleOrders (G := G) (singletonEdgeColoring v c t.1) v s := by
  classical
  simp only [singletonOrders, Finset.mem_filter, Finset.mem_univ, true_and]

theorem singletonOrders_card_le_fourteen (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) (s : Finset (Sym2 V)) :
    (singletonOrders v c s).card ≤ 14 := by
  classical
  by_cases hn : (singletonOrders v c s).Nonempty
  · obtain ⟨t, ht⟩ := hn
    have ht' := (mem_singletonOrders v c s t).mp ht
    have hc : (singletonOrders v c s).card ≤
        (basedCycleOrders (G := G) (singletonEdgeColoring v c t.1) v s).card := by
      apply Finset.card_le_card_of_injOn (fun z => z.2)
      · intro z hz
        rcases z with ⟨j, π⟩
        have hz' := (mem_singletonOrders v c s (j, π)).mp hz
        have hi : j = t.1 := singleton_order_color_eq v c j t.1 π t.2 s hz' ht'
        subst j
        exact hz'
      · intro a ha b hb he
        have hi := singleton_order_color_eq v c a.1 b.1 a.2 b.2 s
          ((mem_singletonOrders v c s a).mp ha) ((mem_singletonOrders v c s b).mp hb)
        exact Prod.ext hi he
    exact hc.trans (basedCycleOrders_card_le_fourteen _ v s)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp

theorem singleton_three_hundred_sixty_per_color_cycles (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7)) :
    360 * (singletonNeighborColors v c).card ≤ (TaskH.modCyclesThrough 7 G v).ncard := by
  classical
  let A : Finset (↥(singletonNeighborColors v c) × Equiv.Perm (Fin 7)) := Finset.univ
  let C := (TaskH.modCyclesThrough_finite 7 G v).toFinset
  let R : (↥(singletonNeighborColors v c) × Equiv.Perm (Fin 7)) →
      Finset (Sym2 V) → Prop := fun t s => t ∈ singletonOrders v c s
  have hperm : Fintype.card (Equiv.Perm (Fin 7)) = 5040 := by norm_num [Fintype.card_perm]
  have hA : A.card = 5040 * (singletonNeighborColors v c).card := by
    simp only [A, Finset.card_univ, Fintype.card_prod, Fintype.card_coe, hperm, Nat.mul_comm]
  have hrow : ∀ t ∈ A, 1 ≤ (C.filter (R t)).card := by
    intro t _ht
    obtain ⟨p, hp, hlen, hf, hy⟩ := singleton_through_ordered_cycle hcrit hs v c t.1 t.2
    have hm : p.edges.toFinset ∈ C.filter (R t) := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · apply (TaskH.modCyclesThrough_finite 7 G v).mem_toFinset.mpr
        have hh := mem_modCyclesThroughAvoid_of_cycle hp hlen hy
        exact ⟨hh.1, hh.2.1⟩
      · apply (mem_singletonOrders v c p.edges.toFinset t).mpr
        apply (mem_basedCycleOrders _ v p.edges.toFinset t.2).mpr
        exact ⟨p, hp, hlen, p.coe_edges_toFinset.symm, hf⟩
    have hpos := Finset.card_pos.mpr ⟨p.edges.toFinset, hm⟩
    omega
  have hcol : ∀ s ∈ C, (A.filter (fun t => R t s)).card ≤ 14 := by
    intro s _hs
    have he : A.filter (fun t => R t s) = singletonOrders v c s := by
      ext t
      simp only [A, R, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he]
    exact singletonOrders_card_le_fourteen v c s
  have hdouble : (∑ t ∈ A, (C.filter (R t)).card) =
      ∑ s ∈ C, (A.filter (fun t => R t s)).card := by
    convert FiniteBudget.relation_double_count A C R using 1 <;>
      apply Finset.sum_congr rfl
    all_goals
      intro z _
      congr 1
      ext w
      simp only [Finset.mem_filter]
  have hlow : A.card ≤ ∑ t ∈ A, (C.filter (R t)).card := by
    calc
      A.card = ∑ _t ∈ A, 1 := by simp
      _ ≤ ∑ t ∈ A, (C.filter (R t)).card := Finset.sum_le_sum hrow
  have hhigh : (∑ s ∈ C, (A.filter (fun t => R t s)).card) ≤ C.card * 14 := by
    calc
      _ ≤ ∑ _s ∈ C, 14 := Finset.sum_le_sum hcol
      _ = C.card * 14 := by simp
  have hmid : (∑ t ∈ A, (C.filter (R t)).card) ≤
      ∑ s ∈ C, (A.filter (fun t => R t s)).card := le_of_eq hdouble
  have htotal : (∑ t ∈ A, (C.filter (R t)).card) ≤ C.card * 14 :=
    Nat.le_trans hmid hhigh
  have hn : 5040 * (singletonNeighborColors v c).card ≤ C.card * 14 := by
    rw [hA] at hlow
    exact Nat.le_trans hlow htotal
  have hC : C.card = (TaskH.modCyclesThrough 7 G v).ncard :=
    (Set.ncard_eq_toFinset_card (TaskH.modCyclesThrough 7 G v)
      (TaskH.modCyclesThrough_finite 7 G v)).symm
  rw [hC] at hn
  omega

theorem critical_singleton_cycle_bound (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (v : V) :
    360 * (14 - G.degree v) ≤ (TaskH.modCyclesThrough 7 G v).ncard := by
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit v
  exact (Nat.mul_le_mul_left 360 (singletonNeighborColors_card_ge hcrit v c)).trans
    (singleton_three_hundred_sixty_per_color_cycles hcrit hs v c)

end TaskH.Seven

#print axioms TaskH.Seven.singletonEdgeColoring
#print axioms TaskH.Seven.singletonEdgeColoring_base
#print axioms TaskH.Seven.singletonEdgeColoring_outside
#print axioms TaskH.Seven.singleton_through_ordered_cycle
#print axioms TaskH.Seven.singleton_cycle_missing_color
#print axioms TaskH.Seven.singleton_cycle_visits_other_color
#print axioms TaskH.Seven.singleton_order_color_eq
#print axioms TaskH.Seven.singletonOrders
#print axioms TaskH.Seven.mem_singletonOrders
#print axioms TaskH.Seven.singletonOrders_card_le_fourteen
#print axioms TaskH.Seven.singleton_three_hundred_sixty_per_color_cycles
#print axioms TaskH.Seven.critical_singleton_cycle_bound
