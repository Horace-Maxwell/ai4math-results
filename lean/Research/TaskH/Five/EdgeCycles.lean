import Research.TaskH.Five.FiveColorPerms
import Research.TaskH.CycleOrientation
import Research.TaskH.Basics

/-!
Critical-edge recolouring produces actual five-cycles under the short-cycle
conclusion of the equality argument. ShortFiveCycles is an internal result
to be derived from the original equality hypotheses, not a new hypothesis
in the frozen Question 2 or CaseFive statements.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open _root_.TaskH.Challenge SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

theorem fiveColorCycle_no_fixed (i : Fin 12) (a : Fin 5) :
    fiveColorCycle i a ≠ a := by
  intro h
  exact fiveColorCycle_no_two_step i a ((congrArg (fiveColorCycle i) h).trans h)

/-- The reverse reachability argument keeps the very same deleted-edge graph
and coloring; no transport of the coloring through a graph equality is used. -/
theorem critical_edge_reachable_from_right (h : IsCriticalPlus 5 G) {x y : V}
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 5)) (σ : Equiv.Perm (Fin 5))
    (hchange : σ (c y) ≠ c y) :
    Relation.ReflTransGen (ColorStep (G.deleteEdges {s(x, y)}) c σ) y x := by
  classical
  by_contra hnot
  let S : Set V := {z | Relation.ReflTransGen
    (ColorStep (G.deleteEdges {s(x, y)}) c σ) y z}
  have hclosed : ∀ {a b : V}, a ∈ S →
      ColorStep (G.deleteEdges {s(x, y)}) c σ a b → b ∈ S := by
    intro a b ha hab
    exact ha.tail hab
  let d := recolorClosed c σ S hclosed
  have hd : d x = d y := deletedEdge_coloring_endpoints h d
  have hy : y ∈ S := Relation.ReflTransGen.refl
  have hx : x ∉ S := hnot
  have hxv : d x = c x := by
    simpa only [ite_eq_right hx] using (recolorClosed_apply c σ S hclosed x)
  have hyv : d y = σ (c y) := by
    simpa only [ite_eq_left hy] using (recolorClosed_apply c σ S hclosed y)
  have he : σ (c y) = c x := hyv.symm.trans (hd.symm.trans hxv)
  exact hchange (he.trans (deletedEdge_coloring_endpoints h c))

/-- A five-step following closed walk visits its base color only at its base vertex. -/
theorem follows_five_cycle_avoids_same_color {x y : V} (p : G.Walk x x)
    (c : V → Fin 5) (i : Fin 12) (hf : Follows p c (fiveColorCycle i))
    (hl : p.length = 5) (he : c y = c x) (hne : x ≠ y) : y ∉ p.support := by
  intro hy
  obtain ⟨n, hn, hny⟩ := List.mem_iff_getElem.mp hy
  have hn' : n ≤ p.length := by
    rw [Walk.length_support] at hn
    omega
  have hv : p.getVert n = y := (p.getVert_eq_support_getElem hn').trans hny
  have hc : (fiveColorCycle i ^ n) (c x) = c x :=
    (follows_getVert p c (fiveColorCycle i) hf n hn').symm.trans
      ((congrArg c hv).trans he)
  have hd : 5 ∣ n := (fiveColorCycle_pow_fixed_iff i (c x) n).mp hc
  have hn04 : n = 0 ∨ n = 5 := by
    obtain ⟨t, ht⟩ := hd
    omega
  rcases hn04 with hn0 | hn4
  · exact hne (by simpa only [hn0, Walk.getVert_zero] using hv)
  · have h4 : p.getVert 5 = x := by simpa only [hl] using p.getVert_length
    exact hne (h4.symm.trans (hn4 ▸ hv))

/-- For each of the three five-color cyclic orders, an actual cycle through x
avoids the other endpoint y of the deleted critical edge. -/
theorem critical_edge_five_cycle (h : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    {x y : V} (hxy : G.Adj x y)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 5)) (i : Fin 12) :
    ∃ q : G.Walk x x, q.IsCycle ∧ q.length = 5 ∧
      Follows q c (fiveColorCycle i) ∧ y ∉ q.support := by
  have hmono : ColorStep (G.deleteEdges {s(x, y)}) c (fiveColorCycle i) ≤
      ColorStep G c (fiveColorCycle i) := by
    intro a b hab
    exact ⟨(SimpleGraph.deleteEdges_adj.mp hab.1).1, hab.2⟩
  have hrxy := Relation.ReflTransGen.mono hmono x y
    (critical_edge_reachable h c (fiveColorCycle i) (fiveColorCycle_no_fixed i (c x)))
  have hryx := Relation.ReflTransGen.mono hmono y x
    (critical_edge_reachable_from_right h c (fiveColorCycle i)
      (fiveColorCycle_no_fixed i (c y)))
  obtain ⟨p, hp⟩ := reach_exists_follows_walk c (fiveColorCycle i) hrxy
  obtain ⟨r, hr⟩ := reach_exists_follows_walk c (fiveColorCycle i) hryx
  have hpos : 0 < p.length := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hxy.ne)
  have hnon : p.append r ≠ .nil := by
    intro heq
    have hz := congrArg Walk.length heq
    simp only [Walk.length_append, Walk.length_nil] at hz
    omega
  have hf := (follows_append p r c (fiveColorCycle i)).mpr ⟨hp, hr⟩
  obtain ⟨q, hq, hqf⟩ := follows_closed_exists_cycle (p.append r) hnon c
    (fiveColorCycle i) hf (fiveColorCycle_no_two_step i (c x))
  have hlen := hs q hq (follows_fiveColorCycle_length_dvd q c i hqf)
  refine ⟨q, hq, hlen, hqf, ?_⟩
  exact follows_five_cycle_avoids_same_color q c i hqf hlen
    (deletedEdge_coloring_endpoints h c).symm hxy.ne

theorem mem_modCyclesThroughAvoid_of_cycle [DecidableEq V] {x y : V}
    {p : G.Walk x x} (hp : p.IsCycle) (hlen : p.length = 5) (hy : y ∉ p.support) :
    p.edges.toFinset ∈ TaskH.modCyclesThroughAvoid 5 G x y := by
  refine ⟨(Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr ?_, ?_, ?_⟩
  · simpa only [hlen] using (dvd_refl 5)
  · exact (TaskH.cycleContains_edges_toFinset_iff p hp.not_nil x).mpr p.start_mem_support
  · intro he
    exact hy ((TaskH.cycleContains_edges_toFinset_iff p hp.not_nil y).mp he)

end TaskH.Five

#print axioms TaskH.Five.fiveColorCycle_no_fixed
#print axioms TaskH.Five.critical_edge_reachable_from_right
#print axioms TaskH.Five.follows_five_cycle_avoids_same_color
#print axioms TaskH.Five.critical_edge_five_cycle
#print axioms TaskH.Five.mem_modCyclesThroughAvoid_of_cycle
