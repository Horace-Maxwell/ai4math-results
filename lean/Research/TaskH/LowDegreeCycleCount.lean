import Research.TaskH.LowDegreeCycles

/-!
The twelve degree-four cycles are distinct actual undirected edge sets.
Within an assigned color this uses the three cyclic-order representatives;
between assigned colors it proves the different missing colors from actual
following walks. No abstract budget or coverage premise is assumed.
-/

set_option autoImplicit false

universe u

namespace TaskH

open Challenge SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

theorem fourColorCycle_orbit_covers (j : Fin 3) (a b : Fin 4) :
    ∃ r : Fin 4, (fourColorCycle j ^ r.val) a = b := by
  have h : ∀ (j : Fin 3) (a b : Fin 4), ∃ r : Fin 4,
      (fourColorCycle j ^ r.val) a = b := by decide +kernel
  exact h j a b

section FiniteGraph

variable [Fintype V] [DecidableRel G.Adj]

theorem degreeFourCycle_missing_color (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i : Fin 4) (j : Fin 3) (z : {x : V // x ≠ v})
    (hz : z.val ∈ (degreeFourCycle hcrit hs v c hdegree i j).support) : c z ≠ i := by
  intro hc
  have he : degreeFourEdgeColoring hcrit v c hdegree i z.val =
      degreeFourEdgeColoring hcrit v c hdegree i v := by
    rw [degreeFourEdgeColoring_outside hcrit v c hdegree i z.val z.property,
      degreeFourEdgeColoring_base]
    exact hc
  exact follows_four_cycle_avoids_same_color (degreeFourCycle hcrit hs v c hdegree i j)
    (degreeFourEdgeColoring hcrit v c hdegree i) j
    (degreeFourCycle_follows hcrit hs v c hdegree i j)
    (degreeFourCycle_length hcrit hs v c hdegree i j) he z.property.symm hz

theorem degreeFourCycle_visits_other_color
    (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i t : Fin 4) (j : Fin 3) (hit : i ≠ t) :
    ∃ z : {x : V // x ≠ v}, c z = t ∧
      z.val ∈ (degreeFourCycle hcrit hs v c hdegree i j).support := by
  obtain ⟨r, hr⟩ := fourColorCycle_orbit_covers j i t
  have hr0 : r.val ≠ 0 := by
    intro he
    apply hit
    simpa only [he, pow_zero, Equiv.Perm.one_apply] using hr
  have hrpos : 0 < r.val := by omega
  let p := degreeFourCycle hcrit hs v c hdegree i j
  have hp : p.IsCycle := degreeFourCycle_isCycle hcrit hs v c hdegree i j
  have hlen : p.length = 4 := degreeFourCycle_length hcrit hs v c hdegree i j
  have hzv : p.getVert r.val ≠ v := by
    intro he
    have he' := (hp.getVert_endpoint_iff (by have := r.isLt; omega)).mp he
    have := r.isLt
    omega
  let z : {x : V // x ≠ v} := ⟨p.getVert r.val, hzv⟩
  have hfollow := follows_getVert p (degreeFourEdgeColoring hcrit v c hdegree i)
    (fourColorCycle j) (degreeFourCycle_follows hcrit hs v c hdegree i j)
    r.val (by have := r.isLt; omega)
  rw [degreeFourEdgeColoring_base] at hfollow
  have hzassigned : degreeFourEdgeColoring hcrit v c hdegree i z.val = t :=
    hfollow.trans hr
  have hzcolor : c z = t :=
    (degreeFourEdgeColoring_outside hcrit v c hdegree i z.val z.property).symm.trans hzassigned
  exact ⟨z, hzcolor, p.getVert_mem_support r.val⟩

section DecidableVertices

variable [DecidableEq V]

theorem degreeFourCycle_color_index_eq
    (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i i' : Fin 4) (j j' : Fin 3)
    (he : (degreeFourCycle hcrit hs v c hdegree i j).edges.toFinset =
      (degreeFourCycle hcrit hs v c hdegree i' j').edges.toFinset) : i = i' := by
  by_contra hne
  obtain ⟨z, hzcolor, hzmem⟩ := degreeFourCycle_visits_other_color
    hcrit hs v c hdegree i' i j' (Ne.symm hne)
  have hzcontains : CycleContains (degreeFourCycle hcrit hs v c hdegree i j).edges.toFinset z.val := by
    rw [he]
    exact (cycleContains_edges_toFinset_iff _
      (degreeFourCycle_isCycle hcrit hs v c hdegree i' j').not_nil z.val).mpr hzmem
  have hzmem' := (cycleContains_edges_toFinset_iff _
    (degreeFourCycle_isCycle hcrit hs v c hdegree i j).not_nil z.val).mp hzcontains
  exact degreeFourCycle_missing_color hcrit hs v c hdegree i j z hzmem' hzcolor

theorem degreeFourCycle_indices_eq
    (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4)
    (i i' : Fin 4) (j j' : Fin 3)
    (he : (degreeFourCycle hcrit hs v c hdegree i j).edges.toFinset =
      (degreeFourCycle hcrit hs v c hdegree i' j').edges.toFinset) : i = i' ∧ j = j' := by
  have hi := degreeFourCycle_color_index_eq hcrit hs v c hdegree i i' j j' he
  subst i'
  refine ⟨rfl, ?_⟩
  exact follows_four_cycles_index_eq (degreeFourCycle_isCycle hcrit hs v c hdegree i j)
    (degreeFourCycle_isCycle hcrit hs v c hdegree i j')
    (degreeFourCycle_length hcrit hs v c hdegree i j)
    (degreeFourEdgeColoring hcrit v c hdegree i) j j'
    (degreeFourCycle_follows hcrit hs v c hdegree i j)
    (degreeFourCycle_follows hcrit hs v c hdegree i j') he

theorem degreeFourCycle_edges_injective
    (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4) :
    Function.Injective (fun t : Fin 4 × Fin 3 =>
      (degreeFourCycle hcrit hs v c hdegree t.1 t.2).edges.toFinset) := by
  intro a b he
  obtain ⟨hi, hj⟩ := degreeFourCycle_indices_eq hcrit hs v c hdegree a.1 b.1 a.2 b.2 he
  exact Prod.ext hi hj

end DecidableVertices

theorem degreeFour_twelve_cycles_through
    (hcrit : IsCriticalPlus 4 G) (hs : ShortFourCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 4)) (hdegree : G.degree v = 4) :
    12 ≤ ({s : Finset (Sym2 V) | s ∈ ModCycleEdgeSets 4 G ∧ CycleContains s v} :
      Set (Finset (Sym2 V))).ncard := by
  classical
  let E : Fin 4 × Fin 3 → Finset (Sym2 V) :=
    fun t => (degreeFourCycle hcrit hs v c hdegree t.1 t.2).edges.toFinset
  have hinj : Function.Injective E := degreeFourCycle_edges_injective hcrit hs v c hdegree
  let C : Set (Finset (Sym2 V)) :=
    {s | s ∈ ModCycleEdgeSets 4 G ∧ CycleContains s v}
  have hE : ∀ t, E t ∈ C := by
    intro t
    have hp := degreeFourCycle_isCycle hcrit hs v c hdegree t.1 t.2
    have hl := degreeFourCycle_length hcrit hs v c hdegree t.1 t.2
    refine ⟨(Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr ?_, ?_⟩
    · simpa only [hl] using (dvd_refl 4)
    · exact (cycleContains_edges_toFinset_iff _ hp.not_nil v).mpr
        (degreeFourCycle hcrit hs v c hdegree t.1 t.2).start_mem_support
  have hcard : (Finset.univ.image E).card = 12 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    norm_num
  have hsub : (((Finset.univ.image E) : Finset (Finset (Sym2 V))) :
      Set (Finset (Sym2 V))) ⊆ C := by
    intro s hs
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hs
    rw [← ht]
    exact hE t
  have hn := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard] at hn
  exact hn

end FiniteGraph

end TaskH

#print axioms TaskH.fourColorCycle_orbit_covers
#print axioms TaskH.degreeFourCycle_missing_color
#print axioms TaskH.degreeFourCycle_visits_other_color
#print axioms TaskH.degreeFourCycle_edges_injective
#print axioms TaskH.degreeFour_twelve_cycles_through
