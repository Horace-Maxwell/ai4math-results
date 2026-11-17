import Research.TaskH.Five.SingletonNeighborColors
import Research.TaskH.Five.EdgeCyclesDistinct

/-!
Each actual singleton neighbor color supplies twelve actual five-cycles
through the deleted vertex. Missing colors distinguish the families, so the
fiber count becomes a lower bound in the original cycle-edge-set collection.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph _root_.TaskH.Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def singletonEdgeColoring (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (i : ↥(singletonNeighborColors v c)) :
    (G.deleteEdges {s(v, (singletonNeighbor v c i).val)}).Coloring (Fin 5) := by
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
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (i : ↥(singletonNeighborColors v c)) : singletonEdgeColoring v c i v = i.val := by
  classical
  change (if hx : v = v then i.val else c ⟨v, hx⟩) = i.val
  exact dite_eq_left rfl

theorem singletonEdgeColoring_outside (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (i : ↥(singletonNeighborColors v c)) (x : V) (hx : x ≠ v) :
    singletonEdgeColoring v c i x = c ⟨x, hx⟩ := by
  classical
  change (if h : x = v then i.val else c ⟨x, h⟩) = c ⟨x, hx⟩
  exact dite_eq_right hx

theorem singleton_through_cycle (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (i : ↥(singletonNeighborColors v c)) (j : Fin 12) :
    ∃ p : G.Walk v v, p.IsCycle ∧ p.length = 5 ∧
      Follows p (singletonEdgeColoring v c i) (fiveColorCycle j) ∧
      (singletonNeighbor v c i).val ∉ p.support :=
  critical_edge_five_cycle hcrit hs (singletonNeighbor v c i).property
    (singletonEdgeColoring v c i) j

noncomputable def singletonCycle (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (i : ↥(singletonNeighborColors v c)) (j : Fin 12) : G.Walk v v :=
  Classical.choose (singleton_through_cycle hcrit hs v c i j)

theorem singletonCycle_spec (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (i : ↥(singletonNeighborColors v c)) (j : Fin 12) :
    (singletonCycle hcrit hs v c i j).IsCycle ∧
      (singletonCycle hcrit hs v c i j).length = 5 ∧
      Follows (singletonCycle hcrit hs v c i j) (singletonEdgeColoring v c i) (fiveColorCycle j) ∧
      (singletonNeighbor v c i).val ∉ (singletonCycle hcrit hs v c i j).support :=
  Classical.choose_spec (singleton_through_cycle hcrit hs v c i j)

theorem fiveColorCycle_orbit_covers (j : Fin 12) (a b : Fin 5) :
    ∃ r : Fin 5, (fiveColorCycle j ^ r.val) a = b := by
  have h : ∀ (j : Fin 12) (a b : Fin 5), ∃ r : Fin 5,
      (fiveColorCycle j ^ r.val) a = b := by decide +kernel
  exact h j a b

theorem singletonCycle_missing_color (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (i : ↥(singletonNeighborColors v c)) (j : Fin 12) (z : {x : V // x ≠ v})
    (hz : z.val ∈ (singletonCycle hcrit hs v c i j).support) : c z ≠ i.val := by
  intro hc
  have he : singletonEdgeColoring v c i z.val = singletonEdgeColoring v c i v := by
    rw [singletonEdgeColoring_outside v c i z.val z.property, singletonEdgeColoring_base]
    exact hc
  exact follows_five_cycle_avoids_same_color (singletonCycle hcrit hs v c i j)
    (singletonEdgeColoring v c i) j (singletonCycle_spec hcrit hs v c i j).2.2.1
    (singletonCycle_spec hcrit hs v c i j).2.1 he z.property.symm hz

theorem singletonCycle_visits_other_color (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (i : ↥(singletonNeighborColors v c)) (t : Fin 5) (j : Fin 12) (hit : i.val ≠ t) :
    ∃ z : {x : V // x ≠ v}, c z = t ∧ z.val ∈ (singletonCycle hcrit hs v c i j).support := by
  obtain ⟨r, hr⟩ := fiveColorCycle_orbit_covers j i.val t
  have hr0 : r.val ≠ 0 := by
    intro he
    apply hit
    simpa only [he, pow_zero, Equiv.Perm.one_apply] using hr
  let p := singletonCycle hcrit hs v c i j
  have hp : p.IsCycle := (singletonCycle_spec hcrit hs v c i j).1
  have hlen : p.length = 5 := (singletonCycle_spec hcrit hs v c i j).2.1
  have hzv : p.getVert r.val ≠ v := by
    intro he
    have he' := (hp.getVert_endpoint_iff (by have := r.isLt; omega)).mp he
    have := r.isLt
    omega
  let z : {x : V // x ≠ v} := ⟨p.getVert r.val, hzv⟩
  have hfollow := follows_getVert p (singletonEdgeColoring v c i) (fiveColorCycle j)
    (singletonCycle_spec hcrit hs v c i j).2.2.1 r.val (by have := r.isLt; omega)
  rw [singletonEdgeColoring_base] at hfollow
  have hzassigned : singletonEdgeColoring v c i z.val = t := hfollow.trans hr
  have hzcolor : c z = t :=
    (singletonEdgeColoring_outside v c i z.val z.property).symm.trans hzassigned
  exact ⟨z, hzcolor, p.getVert_mem_support r.val⟩

theorem singletonCycle_color_index_eq (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (i i' : ↥(singletonNeighborColors v c)) (j j' : Fin 12)
    (he : (singletonCycle hcrit hs v c i j).edges.toFinset =
      (singletonCycle hcrit hs v c i' j').edges.toFinset) : i = i' := by
  by_contra hne
  have hneval : i.val ≠ i'.val := fun hv => hne (Subtype.ext hv)
  obtain ⟨z, hzcolor, hzmem⟩ := singletonCycle_visits_other_color
    hcrit hs v c i' i.val j' (Ne.symm hneval)
  have hzcontains : CycleContains (singletonCycle hcrit hs v c i j).edges.toFinset z.val := by
    rw [he]
    exact (cycleContains_edges_toFinset_iff _ (singletonCycle_spec hcrit hs v c i' j').1.not_nil
      z.val).mpr hzmem
  have hzmem' := (cycleContains_edges_toFinset_iff _ (singletonCycle_spec hcrit hs v c i j).1.not_nil
    z.val).mp hzcontains
  exact singletonCycle_missing_color hcrit hs v c i j z hzmem' hzcolor

theorem singletonCycle_edges_injective (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) :
    Function.Injective (fun t : ↥(singletonNeighborColors v c) × Fin 12 =>
      (singletonCycle hcrit hs v c t.1 t.2).edges.toFinset) := by
  intro a b he
  have hi := singletonCycle_color_index_eq hcrit hs v c a.1 b.1 a.2 b.2 he
  have hj : a.2 = b.2 := by
    have he' : (singletonCycle hcrit hs v c a.1 a.2).edges.toFinset =
        (singletonCycle hcrit hs v c a.1 b.2).edges.toFinset := by simpa only [hi] using he
    exact follows_five_cycles_index_eq (singletonCycle_spec hcrit hs v c a.1 a.2).1
      (singletonCycle_spec hcrit hs v c a.1 b.2).1
      (singletonCycle_spec hcrit hs v c a.1 a.2).2.1 (singletonEdgeColoring v c a.1) a.2 b.2
      (singletonCycle_spec hcrit hs v c a.1 a.2).2.2.1
      (singletonCycle_spec hcrit hs v c a.1 b.2).2.2.1 he'
  exact Prod.ext hi hj

theorem singleton_twelve_per_color_cycles (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 5)) :
    12 * (singletonNeighborColors v c).card ≤ (modCyclesThrough 5 G v).ncard := by
  classical
  let E : ↥(singletonNeighborColors v c) × Fin 12 → Finset (Sym2 V) :=
    fun t => (singletonCycle hcrit hs v c t.1 t.2).edges.toFinset
  have hinj : Function.Injective E := singletonCycle_edges_injective hcrit hs v c
  have hE : ∀ t, E t ∈ modCyclesThrough 5 G v := by
    intro t
    have hp := (singletonCycle_spec hcrit hs v c t.1 t.2).1
    have hl := (singletonCycle_spec hcrit hs v c t.1 t.2).2.1
    refine ⟨(Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr ?_, ?_⟩
    · simpa only [hl] using (dvd_refl 5)
    · exact (cycleContains_edges_toFinset_iff _ hp.not_nil v).mpr
        (singletonCycle hcrit hs v c t.1 t.2).start_mem_support
  have hcard : (Finset.univ.image E).card = 12 * (singletonNeighborColors v c).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
      Fintype.card_coe, Fintype.card_fin, Nat.mul_comm]
  have hsub : (((Finset.univ.image E) : Finset (Finset (Sym2 V))) :
      Set (Finset (Sym2 V))) ⊆ modCyclesThrough 5 G v := by
    intro s hs'
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hs'
    rw [← ht]
    exact hE t
  have hn := Set.ncard_le_ncard hsub (modCyclesThrough_finite 5 G v)
  rw [Set.ncard_coe_finset, hcard] at hn
  exact hn

theorem critical_singleton_cycle_bound (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (v : V) : 12 * (10 - G.degree v) ≤ (modCyclesThrough 5 G v).ncard := by
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit v
  exact (Nat.mul_le_mul_left 12 (singletonNeighborColors_card_ge hcrit v c)).trans
    (singleton_twelve_per_color_cycles hcrit hs v c)

end TaskH.Five

#print axioms TaskH.Five.singletonEdgeColoring
#print axioms TaskH.Five.singletonEdgeColoring_base
#print axioms TaskH.Five.singletonEdgeColoring_outside
#print axioms TaskH.Five.singleton_through_cycle
#print axioms TaskH.Five.singletonCycle
#print axioms TaskH.Five.singletonCycle_spec
#print axioms TaskH.Five.fiveColorCycle_orbit_covers
#print axioms TaskH.Five.singletonCycle_missing_color
#print axioms TaskH.Five.singletonCycle_visits_other_color
#print axioms TaskH.Five.singletonCycle_color_index_eq
#print axioms TaskH.Five.singletonCycle_edges_injective
#print axioms TaskH.Five.singleton_twelve_per_color_cycles
#print axioms TaskH.Five.critical_singleton_cycle_bound
