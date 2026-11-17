import Research.TaskH.Seven.SevenSCCRelation
import Research.TaskH.Seven.SevenEqualityBasics

/-! Actual nonbad circles and actual directed circles in every successor
component. Original equality wrappers discharge the incidence assumptions. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

theorem follows_relation_reach {A : Type*} (c : V → A) (σ : Equiv.Perm A)
    (R : V → V → Prop)
    (hmono : ∀ ⦃a b : V⦄, ColorStep G c σ a b → R a b)
    {x y : V} (p : G.Walk x y) (hf : Follows p c σ) :
    Relation.ReflTransGen R x y := by
  revert hf
  induction p with
  | nil => intro _; exact Relation.ReflTransGen.refl
  | @cons x y z hxy p ih =>
    intro hf
    have hparts := (follows_cons hxy p c σ).mp hf
    exact (Relation.ReflTransGen.single (hmono ⟨hxy, hparts.1⟩)).trans
      (ih hparts.2)

theorem follows_relation_support {A : Type*} (c : V → A) (σ : Equiv.Perm A)
    (R : V → V → Prop)
    (hmono : ∀ ⦃a b : V⦄, ColorStep G c σ a b → R a b)
    {x y : V} (p : G.Walk x y) (hf : Follows p c σ)
    {a : V} (ha : a ∈ p.support) :
    Relation.ReflTransGen R x a ∧ Relation.ReflTransGen R a y := by
  obtain ⟨q, r, he⟩ := Walk.mem_support_iff_exists_append.mp ha
  have hparts : Follows q c σ ∧ Follows r c σ := by
    rw [he] at hf
    exact (follows_append q r c σ).mp hf
  exact ⟨follows_relation_reach c σ R hmono q hparts.1,
    follows_relation_reach c σ R hmono r hparts.2⟩

/-- A successor edge cannot be the deleted edge, whose endpoints have
the same color. This uses actual adjacency, not a presumed arc coverage. -/
theorem colorStep_deleteEdge_of_same_color {x y : V} (c : V → Fin 7)
    (σ : Equiv.Perm (Fin 7)) (he : c x = c y)
    (hfix : ∀ a : Fin 7, σ a ≠ a) {a b : V}
    (hab : ColorStep G c σ a b) :
    ColorStep (G.deleteEdges {s(x, y)}) c σ a b := by
  refine ⟨SimpleGraph.deleteEdges_adj.mpr ⟨hab.1, ?_⟩, hab.2⟩
  intro hm
  have heq : s(a, b) = s(x, y) := Set.mem_singleton_iff.mp hm
  rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hc : c y = σ (c x) := by simpa only [ha, hb] using hab.2
    exact hfix (c x) (hc.symm.trans he.symm)
  · have hc : c x = σ (c y) := by simpa only [ha, hb] using hab.2
    exact hfix (c y) (hc.symm.trans he)

theorem following_circle_support_in_component [Fintype V] {x y z : V}
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (he : c x = c y)
    (p : G.Walk z z) (hf : Follows p c (orderedColorCycle π))
    {a : V} (ha : a ∈ p.support) :
    a ∈ successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) z := by
  apply (mem_successorComponent c (orderedColorCycle π) z a).mpr
  exact follows_relation_support c (orderedColorCycle π)
    (ColorStep (G.deleteEdges {s(x, y)}) c (orderedColorCycle π))
    (fun {a b} hab => colorStep_deleteEdge_of_same_color (G := G) (a := a) (b := b)
      c (orderedColorCycle π) he (orderedColorCycle_no_fixed π) hab) p hf ha

/-- The bypass construction retains the prescribed first actual edge.
It is stronger than merely finding an unspecified directed circle. -/
theorem follows_cycle_through_arc {A : Type*} (c : V → A) (σ : Equiv.Perm A)
    {a b : V} (hab : G.Adj a b) (hcolor : c b = σ (c a))
    (hret : Relation.ReflTransGen (ColorStep G c σ) b a)
    (hchange : σ (σ (c a)) ≠ c a) :
    ∃ q : G.Walk a a, q.IsCycle ∧ Follows q c σ ∧ s(a, b) ∈ q.edges := by
  classical
  obtain ⟨r, hr⟩ := reach_exists_follows_walk c σ hret
  have hbypass := follows_bypass r c σ hr
  have hnot : s(a, b) ∉ r.bypass.edges := by
    intro hm
    have hm' : s(b, a) ∈ r.bypass.edges := by simpa only [Sym2.eq_swap] using hm
    have hc := isPath_follows_edge_at_start r.bypass r.bypass_isPath c σ hbypass hm'
    apply hchange
    rw [← hcolor, ← hc]
  refine ⟨.cons hab r.bypass, ?_, ?_, ?_⟩
  · exact (Walk.cons_isCycle_iff ..).mpr ⟨r.bypass_isPath, hnot⟩
  · exact (follows_cons hab r.bypass c σ).mpr ⟨hcolor, hbypass⟩
  · simp [Walk.edges_cons]

noncomputable def sccBadCircleFinset [Fintype V] (G : SimpleGraph V) (x y : V) :
    Finset (Finset (Sym2 V)) :=
  (cycleFinset G).filter (fun s => CycleContains s x ∧ CycleContains s y)

theorem exists_nonbad_circle_through [Fintype V] (hs : ShortSevenCycles G)
    (hdeg : ∀ z : V, 361 ≤ cycleDegree G z) {x y : V}
    (hbad : (sccBadCircleFinset G x y).card ≤ 78) (z : V) :
    ∃ a : V, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 7 ∧
      z ∈ p.support ∧ (x ∉ p.support ∨ y ∉ p.support) := by
  classical
  have hlt : (sccBadCircleFinset G x y).card < (throughFinset G z).card := by
    have hz := hdeg z
    change 361 ≤ (throughFinset G z).card at hz
    omega
  obtain ⟨C, hC, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hCm := (mem_throughFinset C z).mp hC
  obtain ⟨a, p, hp, he, hdiv⟩ := Basics.mem_modCycleEdgeSets_iff.mp hCm.1
  have hz : z ∈ p.support := by
    apply (cycleContains_edges_toFinset_iff p hp.not_nil z).mp
    simpa only [he] using hCm.2
  refine ⟨a, p, hp, hs p hp hdiv, hz, ?_⟩
  by_cases hx : x ∈ p.support
  · right
    intro hy
    apply hnot
    apply Finset.mem_filter.mpr
    refine ⟨(mem_cycleFinset C).mpr hCm.1, ?_, ?_⟩
    · rw [← he]
      exact (cycleContains_edges_toFinset_iff p hp.not_nil x).mpr hx
    · rw [← he]
      exact (cycleContains_edges_toFinset_iff p hp.not_nil y).mpr hy
  · exact Or.inl hx

theorem equality_exists_nonbad_circle_through [Fintype V] [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    {x y : V} (hbad : (sccBadCircleFinset G x y).card ≤ 78) (z : V) :
    ∃ a : V, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = 7 ∧
      z ∈ p.support ∧ (x ∉ p.support ∨ y ∉ p.support) :=
  exists_nonbad_circle_through (equality_shortSevenCycles hcrit hc)
    (equality_three_hundred_sixty_one_le_cycleDegree hcrit hc) hbad z

theorem successorComponent_has_other [Fintype V] (hr : RainbowSevenCycles G)
    (hs : ShortSevenCycles G) (hdeg : ∀ z : V, 361 ≤ cycleDegree G z)
    {x y : V} (hbad : (sccBadCircleFinset G x y).card ≤ 78)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (z : V) :
    ∃ t : V, z ≠ t ∧
      SuccessorEquivalent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) z t := by
  obtain ⟨a, p, hp, hl, hz, hav⟩ := exists_nonbad_circle_through hs hdeg hbad z
  by_cases hza : z = a
  · subst z
    refine ⟨p.snd, (p.adj_snd hp.not_nil).ne, ?_⟩
    exact nonbad_cycle_successorEquivalent hr p hp hl hav c π
      p.start_mem_support (p.getVert_mem_support 1)
  · exact ⟨a, hza, nonbad_cycle_successorEquivalent hr p hp hl hav c π
      hz p.start_mem_support⟩

theorem successorComponent_vertex_cycle [Fintype V]
    (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hdeg : ∀ z : V, 361 ≤ cycleDegree G z)
    {x y : V} (hbad : (sccBadCircleFinset G x y).card ≤ 78)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7)) (he : c x = c y)
    (π : Equiv.Perm (Fin 7)) (z : V) :
    ∃ q : G.Walk z z, q.IsCycle ∧ q.length = 7 ∧
      Follows q c (orderedColorCycle π) ∧
      ∀ a ∈ q.support,
        a ∈ successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) z := by
  obtain ⟨t, hzt, ht⟩ := successorComponent_has_other hr hs hdeg hbad c π z
  have hmono : ColorStep (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) ≤
      ColorStep G c (orderedColorCycle π) := by
    intro a b hab
    exact ⟨(SimpleGraph.deleteEdges_adj.mp hab.1).1, hab.2⟩
  obtain ⟨p, hp⟩ := reach_exists_follows_walk c (orderedColorCycle π)
    (Relation.ReflTransGen.mono hmono z t ht.1)
  obtain ⟨r, hr'⟩ := reach_exists_follows_walk c (orderedColorCycle π)
    (Relation.ReflTransGen.mono hmono t z ht.2)
  have hn : p.append r ≠ .nil := by
    intro hnil
    have hlen := congrArg Walk.length hnil
    have hpos : 0 < p.length :=
      Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hzt)
    simp only [Walk.length_append, Walk.length_nil] at hlen
    omega
  obtain ⟨q, hq, hqf⟩ := follows_closed_exists_cycle (p.append r) hn c
    (orderedColorCycle π) ((follows_append p r c (orderedColorCycle π)).mpr ⟨hp, hr'⟩)
    (orderedColorCycle_no_two_step π (c z))
  have hqrank := (follows_orderedColorCycle_iff q c π).mp hqf
  refine ⟨q, hq, hs q hq (follows_rotate_seven_length_dvd q _ hqrank), hqf, ?_⟩
  intro a ha
  exact following_circle_support_in_component c π he q hqf ha

theorem equality_successorComponent_vertex_cycle [Fintype V] [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    {x y : V} (hbad : (sccBadCircleFinset G x y).card ≤ 78)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (z : V) :
    ∃ q : G.Walk z z, q.IsCycle ∧ q.length = 7 ∧
      Follows q c (orderedColorCycle π) ∧
      ∀ a ∈ q.support,
        a ∈ successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) z :=
  successorComponent_vertex_cycle (equality_shortSevenCycles hcrit hc)
    (equality_rainbowSevenCycles hcrit hc)
    (equality_three_hundred_sixty_one_le_cycleDegree hcrit hc) hbad c
    (deletedEdge_coloring_endpoints hcrit c) π z

/-- Every actual successor arc internal to a component belongs to an
actual directed C7 wholly contained in that same component. -/
theorem successorComponent_arc_cycle [Fintype V] (hs : ShortSevenCycles G)
    {x y a b d : V} (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (he : c x = c y) (π : Equiv.Perm (Fin 7))
    (hb : b ∈ successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) a)
    (hd : d ∈ successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) a)
    (hbd : ColorStep (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) b d) :
    ∃ q : G.Walk b b, q.IsCycle ∧ q.length = 7 ∧
      Follows q c (orderedColorCycle π) ∧ s(b, d) ∈ q.edges ∧
      ∀ z ∈ q.support,
        z ∈ successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) a := by
  have hab := (mem_successorComponent c (orderedColorCycle π) a b).mp hb
  have had := (mem_successorComponent c (orderedColorCycle π) a d).mp hd
  have hret : Relation.ReflTransGen
      (ColorStep (G.deleteEdges {s(x, y)}) c (orderedColorCycle π)) d b :=
    had.2.trans hab.1
  have hmono : ColorStep (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) ≤
      ColorStep G c (orderedColorCycle π) := by
    intro u v huv
    exact ⟨(SimpleGraph.deleteEdges_adj.mp huv.1).1, huv.2⟩
  obtain ⟨q, hq, hqf, hqe⟩ := follows_cycle_through_arc c (orderedColorCycle π)
    (SimpleGraph.deleteEdges_adj.mp hbd.1).1 hbd.2
    (Relation.ReflTransGen.mono hmono d b hret)
    (orderedColorCycle_no_two_step π (c b))
  have hqrank := (follows_orderedColorCycle_iff q c π).mp hqf
  refine ⟨q, hq, hs q hq (follows_rotate_seven_length_dvd q _ hqrank), hqf, hqe, ?_⟩
  intro z hz
  have hbz := (mem_successorComponent c (orderedColorCycle π) b z).mp
    (following_circle_support_in_component c π he q hqf hz)
  exact (mem_successorComponent c (orderedColorCycle π) a z).mpr
    (successorEquivalent_trans hab hbz)

end TaskH.Seven

#print axioms TaskH.Seven.follows_relation_reach
#print axioms TaskH.Seven.follows_relation_support
#print axioms TaskH.Seven.colorStep_deleteEdge_of_same_color
#print axioms TaskH.Seven.following_circle_support_in_component
#print axioms TaskH.Seven.follows_cycle_through_arc
#print axioms TaskH.Seven.sccBadCircleFinset
#print axioms TaskH.Seven.exists_nonbad_circle_through
#print axioms TaskH.Seven.equality_exists_nonbad_circle_through
#print axioms TaskH.Seven.successorComponent_has_other
#print axioms TaskH.Seven.successorComponent_vertex_cycle
#print axioms TaskH.Seven.equality_successorComponent_vertex_cycle
#print axioms TaskH.Seven.successorComponent_arc_cycle
