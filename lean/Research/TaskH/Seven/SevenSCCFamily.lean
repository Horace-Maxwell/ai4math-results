import Research.TaskH.Seven.SevenSCCCycle
import Research.TaskH.Seven.SevenSCCCover

/-! Complete actual following-circle families in successor components.
Walk transport proves coverage and intersection connectivity; the family
is the graph's genuine unoriented finite edge-set family. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable def sccFollowingCircleFinset (G : SimpleGraph V) {x y : V}
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (a : V) : Finset (Finset (Sym2 V)) :=
  (cycleFinset G).filter (fun C =>
    ∃ z ∈ successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) a,
      ∃ p : G.Walk z z, p.IsCycle ∧ p.length = 7 ∧
        Follows p c (orderedColorCycle π) ∧ p.edges.toFinset = C)

theorem mem_sccFollowingCircleFinset_of_cycle {x y a z : V}
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7)) (π : Equiv.Perm (Fin 7))
    (hz : z ∈ successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) a)
    (p : G.Walk z z) (hp : p.IsCycle) (hl : p.length = 7)
    (hf : Follows p c (orderedColorCycle π)) :
    p.edges.toFinset ∈ sccFollowingCircleFinset G c π a := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨(mem_cycleFinset _).mpr ?_, z, hz, p, hp, hl, hf, rfl⟩
  apply (Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr
  rw [hl]

theorem sccFollowingCircleFinset_support_subset {x y a : V}
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7)) (he : c x = c y)
    (π : Equiv.Perm (Fin 7)) {C : Finset (Sym2 V)}
    (hC : C ∈ sccFollowingCircleFinset G c π a) :
    TaskH.cycleVertices C ⊆
      successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) a := by
  obtain ⟨z, hz, p, hp, _hl, hf, hset⟩ := (Finset.mem_filter.mp hC).2
  have haz := (mem_successorComponent c (orderedColorCycle π) a z).mp hz
  intro w hw
  have hws : w ∈ p.support := by
    apply (cycleContains_edges_toFinset_iff p hp.not_nil w).mp
    rw [hset]
    exact (TaskH.mem_cycleVertices C w).mp hw
  have hzw := (mem_successorComponent c (orderedColorCycle π) z w).mp
    (following_circle_support_in_component c π he p hf hws)
  exact (mem_successorComponent c (orderedColorCycle π) a w).mpr
    (successorEquivalent_trans haz hzw)

theorem sccFollowingCircleFinset_covers (hs : ShortSevenCycles G)
    (hr : RainbowSevenCycles G) (hdeg : ∀ z : V, 361 ≤ cycleDegree G z)
    {x y : V} (hbad : (sccBadCircleFinset G x y).card ≤ 78)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7)) (he : c x = c y)
    (π : Equiv.Perm (Fin 7)) (a : V) :
    (sccFollowingCircleFinset G c π a).biUnion TaskH.cycleVertices =
      successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) a := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨C, hC, hzC⟩ := Finset.mem_biUnion.mp hz
    exact sccFollowingCircleFinset_support_subset c he π hC hzC
  · intro hz
    obtain ⟨p, hp, hl, hf, _hps⟩ := successorComponent_vertex_cycle hs hr hdeg hbad c he π z
    apply Finset.mem_biUnion.mpr
    refine ⟨p.edges.toFinset,
      mem_sccFollowingCircleFinset_of_cycle c π hz p hp hl hf, ?_⟩
    apply (TaskH.mem_cycleVertices _ z).mpr
    exact (cycleContains_edges_toFinset_iff p hp.not_nil z).mpr p.start_mem_support

theorem sccFollowingCircleFinset_nonempty (hs : ShortSevenCycles G)
    (hr : RainbowSevenCycles G) (hdeg : ∀ z : V, 361 ≤ cycleDegree G z)
    {x y : V} (hbad : (sccBadCircleFinset G x y).card ≤ 78)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7)) (he : c x = c y)
    (π : Equiv.Perm (Fin 7)) (a : V) :
    (sccFollowingCircleFinset G c π a).Nonempty := by
  obtain ⟨p, hp, hl, hf, _hps⟩ := successorComponent_vertex_cycle hs hr hdeg hbad c he π a
  exact ⟨p.edges.toFinset, mem_sccFollowingCircleFinset_of_cycle c π
    (successorComponent_self c (orderedColorCycle π) a) p hp hl hf⟩

def ActualCircleIntersection (F : Finset (Finset (Sym2 V)))
    (C D : Finset (Sym2 V)) : Prop :=
  C ∈ F ∧ D ∈ F ∧
    (TaskH.cycleVertices C ∩ TaskH.cycleVertices D).Nonempty

theorem actualCircleIntersection_of_common_vertex
    (F : Finset (Finset (Sym2 V))) {C D : Finset (Sym2 V)}
    (hC : C ∈ F) (hD : D ∈ F) {z : V}
    (hzC : CycleContains C z) (hzD : CycleContains D z) :
    ActualCircleIntersection F C D := by
  refine ⟨hC, hD, z, ?_⟩
  exact Finset.mem_inter.mpr
    ⟨(TaskH.mem_cycleVertices C z).mpr hzC, (TaskH.mem_cycleVertices D z).mpr hzD⟩

/-- Move through a genuine successor walk by inserting the actual circle
carrying each traversed arc. Every new intersection has its actual vertex. -/
theorem follows_walk_links_actual_circles (hs : ShortSevenCycles G)
    {x y a u v : V} (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (he : c x = c y) (π : Equiv.Perm (Fin 7))
    (p : (G.deleteEdges {s(x, y)}).Walk u v) :
    Follows p c (orderedColorCycle π) →
    (∀ z ∈ p.support,
      z ∈ successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) a) →
    ∀ C : Finset (Sym2 V), C ∈ sccFollowingCircleFinset G c π a →
      CycleContains C u →
      ∃ D ∈ sccFollowingCircleFinset G c π a,
        Relation.ReflTransGen (ActualCircleIntersection (sccFollowingCircleFinset G c π a)) C D ∧
        CycleContains D v := by
  classical
  induction p with
  | nil =>
    intro _hf _hps C hC hCu
    exact ⟨C, hC, Relation.ReflTransGen.refl, hCu⟩
  | @cons u w v huw p ih =>
    intro hf hps C hC hCu
    have hparts := (follows_cons huw p c (orderedColorCycle π)).mp hf
    have hu := hps u (Walk.start_mem_support _)
    have hw := hps w (by
      change w ∈ u :: p.support
      exact List.mem_cons_of_mem u p.start_mem_support)
    obtain ⟨q, hq, hql, hqf, hqe, _hqs⟩ :=
      successorComponent_arc_cycle hs c he π hu hw ⟨huw, hparts.1⟩
    have hK := mem_sccFollowingCircleFinset_of_cycle c π hu q hq hql hqf
    have hKu : CycleContains q.edges.toFinset u :=
      (cycleContains_edges_toFinset_iff q hq.not_nil u).mpr q.start_mem_support
    have hKw : CycleContains q.edges.toFinset w :=
      (cycleContains_edges_toFinset_iff q hq.not_nil w).mpr
        (q.snd_mem_support_of_mem_edges hqe)
    have htail : ∀ z ∈ p.support,
        z ∈ successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) a := by
      intro z hz
      exact hps z (by simp only [Walk.support_cons, List.mem_cons]; exact Or.inr hz)
    obtain ⟨D, hD, hlink, hDv⟩ := ih hparts.2 htail q.edges.toFinset hK hKw
    refine ⟨D, hD, ?_, hDv⟩
    exact (Relation.ReflTransGen.single
      (actualCircleIntersection_of_common_vertex _ hC hK hCu hKu)).trans hlink

theorem sccFollowingCircleFinset_connected (hs : ShortSevenCycles G)
    {x y a : V} (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (he : c x = c y) (π : Equiv.Perm (Fin 7))
    {C D : Finset (Sym2 V)}
    (hC : C ∈ sccFollowingCircleFinset G c π a)
    (hD : D ∈ sccFollowingCircleFinset G c π a) :
    Relation.ReflTransGen (ActualCircleIntersection (sccFollowingCircleFinset G c π a)) C D := by
  obtain ⟨u, hu, q, hq, _hql, _hqf, hqset⟩ := (Finset.mem_filter.mp hC).2
  obtain ⟨v, hv, r, hr, _hrl, _hrf, hrset⟩ := (Finset.mem_filter.mp hD).2
  have hau := (mem_successorComponent c (orderedColorCycle π) a u).mp hu
  have hav := (mem_successorComponent c (orderedColorCycle π) a v).mp hv
  have huv := hau.2.trans hav.1
  obtain ⟨p, hp⟩ := reach_exists_follows_walk c (orderedColorCycle π) huv
  have hps : ∀ z ∈ p.support,
      z ∈ successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) a := by
    intro z hz
    have hparts := follows_relation_support c (orderedColorCycle π)
      (ColorStep (G.deleteEdges {s(x, y)}) c (orderedColorCycle π))
      (by intro _ _ hab; exact hab) p hp hz
    exact (mem_successorComponent c (orderedColorCycle π) a z).mpr
      ⟨hau.1.trans hparts.1, hparts.2.trans hav.2⟩
  have hCu : CycleContains C u := by
    rw [← hqset]
    exact (cycleContains_edges_toFinset_iff q hq.not_nil u).mpr q.start_mem_support
  have hDv : CycleContains D v := by
    rw [← hrset]
    exact (cycleContains_edges_toFinset_iff r hr.not_nil v).mpr r.start_mem_support
  obtain ⟨E, hE, hlink, hEv⟩ := follows_walk_links_actual_circles hs c he π p hp hps C hC hCu
  exact hlink.trans (Relation.ReflTransGen.single
    (actualCircleIntersection_of_common_vertex _ hE hD hEv hDv))

/-- The full finite support inequality is now transported to the actual
successor component and its entire actual directed-circle family. -/
theorem successorComponent_card_le_six_circleCard_add_one
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hdeg : ∀ z : V, 361 ≤ cycleDegree G z)
    {x y : V} (hbad : (sccBadCircleFinset G x y).card ≤ 78)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7)) (he : c x = c y)
    (π : Equiv.Perm (Fin 7)) (a : V) :
    (successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) a).card ≤
      6 * (sccFollowingCircleFinset G c π a).card + 1 := by
  classical
  have hsize : ∀ C ∈ sccFollowingCircleFinset G c π a,
      (TaskH.cycleVertices C).card ≤ 7 := by
    intro C hC
    have hmem := (mem_cycleFinset C).mp (Finset.mem_filter.mp hC).1
    exact le_of_eq (cycleVertices_card_seven_of_mem hs hmem)
  have hconnected : ∀ C ∈ sccFollowingCircleFinset G c π a,
      ∀ D ∈ sccFollowingCircleFinset G c π a,
      Relation.ReflTransGen
        (SupportIntersection (sccFollowingCircleFinset G c π a) TaskH.cycleVertices) C D := by
    intro C hC D hD
    change Relation.ReflTransGen
      (ActualCircleIntersection (sccFollowingCircleFinset G c π a)) C D
    exact sccFollowingCircleFinset_connected hs c he π hC hD
  have hbound := finiteFamily_union_card_le (sccFollowingCircleFinset G c π a)
    TaskH.cycleVertices (sccFollowingCircleFinset_nonempty hs hr hdeg hbad c he π a)
    hsize hconnected
  rw [sccFollowingCircleFinset_covers hs hr hdeg hbad c he π a] at hbound
  exact hbound

theorem equality_successorComponent_card_le_six_circleCard_add_one [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    {x y : V} (hbad : (sccBadCircleFinset G x y).card ≤ 78)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (a : V) :
    (successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) a).card ≤
      6 * (sccFollowingCircleFinset G c π a).card + 1 :=
  successorComponent_card_le_six_circleCard_add_one
    (equality_shortSevenCycles hcrit hc) (equality_rainbowSevenCycles hcrit hc)
    (equality_three_hundred_sixty_one_le_cycleDegree hcrit hc) hbad c
    (deletedEdge_coloring_endpoints hcrit c) π a

end TaskH.Seven

#print axioms TaskH.Seven.sccFollowingCircleFinset
#print axioms TaskH.Seven.mem_sccFollowingCircleFinset_of_cycle
#print axioms TaskH.Seven.sccFollowingCircleFinset_support_subset
#print axioms TaskH.Seven.sccFollowingCircleFinset_covers
#print axioms TaskH.Seven.sccFollowingCircleFinset_nonempty
#print axioms TaskH.Seven.ActualCircleIntersection
#print axioms TaskH.Seven.actualCircleIntersection_of_common_vertex
#print axioms TaskH.Seven.follows_walk_links_actual_circles
#print axioms TaskH.Seven.sccFollowingCircleFinset_connected
#print axioms TaskH.Seven.successorComponent_card_le_six_circleCard_add_one
#print axioms TaskH.Seven.equality_successorComponent_card_le_six_circleCard_add_one
